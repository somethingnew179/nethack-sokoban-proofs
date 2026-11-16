import Owner1007.TokenPersistence

namespace Owner1007.TokenAccounting
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition

theorem effect_push_data {board state dir t source ending}
    (checked : step board state dir = some t) (effect : Matches state t (.push source ending)) :
    ∃ result, advance board state.player dir = some source ∧ pushBoulder board state source dir = some result := by
  have sourcePlayer : t.state.player = source := by cases ending <;> simp only [Matches] at effect <;> rcases effect with ⟨_, rest⟩
                                                      <;> first | exact congrArg (fun x : Transition => x.state.player) rest
                                                                  | exact congrArg (fun x : Transition => x.state.player) rest.2
  have isPush : t.pushed = true := by cases ending <;> simp only [Matches] at effect <;> rcases effect with ⟨_, rest⟩
                                     <;> first | exact congrArg Transition.pushed rest
                                                 | exact congrArg Transition.pushed rest.2
  rcases step_cases_full board state dir t checked with walked | pushed
  · obtain ⟨target, _, _, _, _, shape⟩ := walked
    simp only [shape] at isPush
    contradiction
  · obtain ⟨other, result, adjacent, _, _, push, shape⟩ := pushed
    have same : other = source := by simpa only [shape] using sourcePlayer
    subst other
    exact ⟨result, adjacent, push⟩

theorem locked_push_outside {board : Board} {locks : List Cell} (locked : Locked board locks)
    {state : State} {dir : Dir} {t : Transition} {source : Cell} {ending : Ending}
    (inside : locks ⊆ state.boulders) (checked : step board state dir = some t)
    (effect : Matches state t (.push source ending)) : source ∉ locks := by
  obtain ⟨result, adjacent, push⟩ := effect_push_data checked effect
  have clear := step_player_clear board state dir t checked
  have first := push_first_clear board state source dir result push
  intro member
  rcases locked state.player clear.1 dir source member adjacent with hero | blocked
  · exact clear.2.2.1 (inside hero)
  · rcases blocked with diagonal | blocked
    · simp only [first.1] at diagonal
      contradiction
    · obtain ⟨dest, next, floor, door, empty⟩ := first.2
      simp only [next] at blocked
      rcases blocked with wall | door' | box
      · exact wall floor
      · exact door door'
      · exact empty (inside box)

/-- Locks preserve the identities in a selected group, not just occupancy
somewhere in the full state. This permits disjoint terminal-debt charges. -/
theorem locked_update_inside {board : Board} {locks group : List Cell}
    (locked : Locked board locks) {state : State} {dir : Dir} {t : Transition} {outcome : Outcome}
    (inside : locks ⊆ group) (subset : group ⊆ state.boulders)
    (checked : step board state dir = some t) (effect : Matches state t outcome) :
    locks ⊆ update group outcome := by
  cases outcome with
  | walk _ => exact inside
  | push source result =>
    have outside := locked_push_outside locked (fun c h => subset (inside h)) checked effect
    by_cases owner : source ∈ group
    · have kept : locks ⊆ group.erase source := by
        intro cell member
        have different : cell ≠ source := by intro same; exact outside (same ▸ member)
        exact (List.mem_erase_of_ne different).mpr (inside member)
      cases result <;> simp only [update, move, if_pos owner, post]
      · exact fun _ h => List.mem_cons_of_mem _ (kept h)
      · exact kept
    · simpa only [update, move, if_neg owner] using inside

theorem Logged.locked_end_inside {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    (actualUnique : initial.boulders.Nodup) (group : List Cell) (unique : group.Nodup)
    (subset : group ⊆ initial.boulders) (locks : List Cell) (locked : Locked board locks)
    (inside : locks ⊆ group) : locks ⊆ endGroup group outcomes := by
  induction logged generalizing group with
  | nil => exact inside
  | cons head effect tail ih =>
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
    have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual group unique subset
    have nextSubset := GhostSubset.update_subset _ _ _ effect group unique subset
    exact ih nextActual (update group _) nextUnique nextSubset
      (locked_update_inside locked inside subset head effect)

theorem Logged.locked_group_energy {board initial dirs final pushes moves outcomes}
    (logged : Logged board initial dirs final pushes moves outcomes)
    {potential : Potential} (valid : Valid board potential)
    (actualUnique : initial.boulders.Nodup) (group : List Cell) (unique : group.Nodup)
    (subset : group ⊆ initial.boulders) (locks : List Cell) (locked : Locked board locks)
    (lockUnique : locks.Nodup) (inside : locks ⊆ group) :
    debtOf potential locks ≤ energy potential group outcomes := by
  have persists := logged.locked_end_inside actualUnique group unique subset locks locked inside
  have debt := NonlinearFacts.weightSum_le_of_nodup_subset (fun c => -potential.boulder c)
    locks (endGroup group outcomes) (fun c => by have h := valid.nonpositive c; omega) lockUnique persists
  change debtOf potential locks ≤ debtOf potential (endGroup group outcomes) at debt
  have costs := logged.ownSlack_nonnegative valid group
  unfold energy
  omega

#print axioms Logged.locked_group_energy
end Owner1007.TokenAccounting
