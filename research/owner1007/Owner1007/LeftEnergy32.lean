import Owner1007.EnergyFrame32
import Owner1007.LockedTokens

namespace Owner1007.LeftPhases32
open NetHack.Sokoban NetHack.Sokoban.LowerBounds
open NetHack.Sokoban.PatternCorrection NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting

theorem self_shadow_update (group : List Cell) (outcome : Outcome) :
    update group (projectedOutcome group outcome) = update group outcome := by
  cases outcome with
  | walk _ => rfl
  | push source result =>
    by_cases owner : source ∈ group <;> simp only [projectedOutcome, update, move, owner, ↓reduceIte]

theorem shadow_hero (group : List Cell) (outcome : Outcome) :
    nextHero (projectedOutcome group outcome) = nextHero outcome := by
  cases outcome with
  | walk _ => rfl
  | push source result => by_cases owner : source ∈ group <;> simp only [projectedOutcome, owner, ↓reduceIte, nextHero]

/-- Lift the four symbolic phases to every real step, including pushes of
untracked stones. Such pushes become covered shadow walks, never teleports. -/
theorem zero_original_step {state : State} {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    (group : List Cell) (subset : group ⊆ state.boulders) (good : Good group state.player)
    {dir : Dir} {t : Transition} {outcome : Outcome}
    (checked : step soko3_2.board state dir = some t) (effect : Matches state t outcome)
    (zero : slack potential32 (projectedOutcome group outcome) = 0) :
    Bad (update group outcome) ∨ Good (update group outcome) t.state.player := by
  obtain ⟨outside, p, same⟩ := good
  have unique := reached.boulders_nodup (by decide +kernel)
  have oracle := original_matches_shadow soko3_2.board state group unique subset
    (NetHack.Soko32Disjoint.trace_disjoint reached) dir t checked outcome effect
  obtain ⟨k, bound, holes, _, _⟩ := NetHack.SokobanLinearPhases.Map32.trace_hole_order reached
  have holeBound : k < 13 := by omega
  have boxesEqual : project group = project (phase p) := by
    funext cell
    simp only [project, same.contains_eq]
  rw [boxesEqual, holes] at oracle
  have result := zero_oracle_step p ⟨k,holeBound⟩ state.player
    (step_player_clear _ _ _ _ checked).1 outside dir (projectedOutcome group outcome) oracle zero
  have afterPerm : (update group outcome).Perm (update (phase p) (projectedOutcome group outcome)) := by
    rw [←self_shadow_update group outcome]
    exact update_perm same (projectedOutcome group outcome)
  have heroEq : nextHero (projectedOutcome group outcome) = t.state.player :=
    (shadow_hero group outcome).trans (matches_hero state t outcome effect).symm
  rcases result with bad | next
  · apply Or.inl
    rcases bad with left | right
    · exact Or.inl (fun _ h => afterPerm.mem_iff.mpr (left h))
    · exact Or.inr (fun _ h => afterPerm.mem_iff.mpr (right h))
  · apply Or.inr
    rw [heroEq] at next
    obtain ⟨outside, q, perm⟩ := next
    exact ⟨outside, q, afterPerm.trans perm⟩

/-- Zero OWNED slack cannot solve the left block cheaply: either its five
tokens survive, or a frozen pair remains with at least three units of debt. -/
theorem zero_left_energy {state final : State} {dirs : List Dir} {pushes moves : Nat}
    {outcomes : List Outcome}
    (logged : Logged soko3_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko3_2.board soko3_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (good : Good group state.player) (zero : ownSlack potential32 group outcomes = 0)
    (completed : Goal final) : 3 ≤ energy potential32 group outcomes := by
  induction logged generalizing history past pastMoves group with
  | nil current =>
    have conserved := reached.conservation
    have empty : current.holes = [] := completed
    change 16 + current.holes.length = current.boulders.length + 12 at conserved
    rw [empty] at conserved
    obtain ⟨_, p, same⟩ := good
    have count := List.Nodup.length_le_of_subset unique subset
    have equal := same.length_eq
    rw [phase_length p] at equal
    simp only [List.length_nil] at conserved
    omega
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nonnegative := logged_step_slack_nonnegative Generated.soko3_2_potential_valid head effect
    have firstNonnegative := projected_slack_nonnegative potential32 group outcome nonnegative
    have restNonnegative := tail.ownSlack_nonnegative Generated.soko3_2_potential_valid (update group outcome)
    change 0 ≤ ownSlack potential32 (update group outcome) outcomes at restNonnegative
    have firstZero : slack potential32 (projectedOutcome group outcome) = 0 := by
      simp only [ownSlack] at zero
      omega
    have restZero : ownSlack potential32 (update group outcome) outcomes = 0 := by
      simp only [ownSlack] at zero
      omega
    have actualUnique := reached.boulders_nodup (by decide +kernel)
    have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group unique subset
    have nextSubset := GhostSubset.update_subset state t outcome effect group unique subset
    have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
    have next := zero_original_step reached group subset good head effect firstZero
    rw [energy_cons, firstZero, Int.zero_add]
    rcases next with bad | nextGood
    · rcases bad with left | right
      · have bound := tail.locked_group_energy Generated.soko3_2_potential_valid nextActual
          (update group outcome) nextUnique nextSubset [158,159]
          (locked_of_check _ _ (locks32_checked 1)) (by decide +kernel) left
        have value : debtOf potential32 [158,159] = 3 := by decide +kernel
        change debtOf potential32 [158,159] ≤ energy potential32 (update group outcome) outcomes at bound
        rw [value] at bound
        exact bound
      · have bound := tail.locked_group_energy Generated.soko3_2_potential_valid nextActual
          (update group outcome) nextUnique nextSubset [160,161]
          (locked_of_check _ _ (locks32_checked 0)) (by decide +kernel) right
        have value : debtOf potential32 [160,161] = 7 := by decide +kernel
        change debtOf potential32 [160,161] ≤ energy potential32 (update group outcome) outcomes at bound
        rw [value] at bound
        omega
    · exact ih nextReached (update group outcome) nextUnique nextSubset nextGood restZero completed

theorem left_must_pay {dirs final pushes moves outcomes}
    (logged : Logged soko3_2.board soko3_2.initial dirs final pushes moves outcomes)
    (completed : Goal final) (small : pushes ≤ 140) :
    1 ≤ ownSlack potential32 EnergyFrame32.A outcomes := by
  have total := EnergyFrame32.energy_total logged completed
  have reserved := EnergyFrame32.group_energy_five logged completed
  have other := logged.energy_nonnegative Generated.soko3_2_potential_valid EnergyFrame32.B
  have nonnegative := logged.ownSlack_nonnegative Generated.soko3_2_potential_valid EnergyFrame32.A
  change 0 ≤ energy potential32 EnergyFrame32.B outcomes at other
  change 0 ≤ ownSlack potential32 EnergyFrame32.A outcomes at nonnegative
  by_cases paid : 1 ≤ ownSlack potential32 EnergyFrame32.A outcomes
  · exact paid
  have zero : ownSlack potential32 EnergyFrame32.A outcomes = 0 := by omega
  have groupUnique : EnergyFrame32.A.Nodup := by decide +kernel
  have groupSubset : EnergyFrame32.A ⊆ soko3_2.initial.boulders := by decide +kernel
  have initialGood : Good EnergyFrame32.A soko3_2.initial.player := by
    exact ⟨by decide +kernel, 0, List.Perm.refl _⟩
  have left := zero_left_energy logged (Trace.nil _) EnergyFrame32.A groupUnique groupSubset initialGood zero completed
  simp only [Int.ofNat_eq_natCast] at total
  omega

#print axioms zero_left_energy
#print axioms left_must_pay
end Owner1007.LeftPhases32
