import Owner1007.OwnedCorral11
namespace Owner1007.OwnedCorralAny11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.Corral11 Owner1007.PricedCorral11 Owner1007.OwnedCorral11
theorem step_good_except {n : Nat} {board : Board} {holes : List Cell}
    {locks region : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : ClosedExcept board holes locks region paid)
    (unique : ∀ i, (locks i).Nodup)
    {state : State} {group : List Cell} {dir : Dir} {t : Transition} {outcome : Outcome}
    (good : Good locks region state group) (insideActual : group ⊆ state.boulders)
    (holesInside : state.holes ⊆ holes)
    (checked : step board state dir = some t) (effect : Matches state t outcome)
    (avoid : ¬ PaidStep paid group dir t) :
    Good locks region t.state (update group outcome) := by
  obtain ⟨i, heroInside, inside⟩ := good
  have actualInside : locks i ⊆ state.boulders := List.Subset.trans inside insideActual
  have smallCorner := original_corner_projected board state (locks i) actualInside dir t checked
  rcases step_cases_full board state dir t checked with walked | pushed
  · obtain ⟨target, adjacent, floor, notBox, notHole, shape⟩ := walked
    have same := matches_unique state t (.walk target) outcome shape effect
    subst outcome
    have door := FiniteTopology.step_target_not_door board state dir t target adjacent checked
    have notLock : target ∉ locks i := fun h => notBox (actualInside h)
    have targetInside := closed.1 i state.player heroInside dir target adjacent floor door notLock smallCorner
    exact ⟨i, by simpa only [shape] using targetInside, inside⟩
  · obtain ⟨source, result, adjacent, floor, present, push, shape⟩ := pushed
    have first := push_first_clear board state source dir result push
    have spec := pushBoulder_spec board state source dir result push
    have actualEffect : Matches state t (.push source (ending result)) := by
      rcases spec.1 with stay | fill
      · simp only [ending,stay.1]
        refine ⟨present, ?_⟩
        simpa only [stay.1,stay.2,afterFill] using shape
      · simp only [ending,fill.1]
        refine ⟨present, fill.2.1, ?_⟩
        simpa only [fill.1,fill.2.2,afterFill] using shape
    have same := matches_unique state t (.push source (ending result)) outcome actualEffect effect
    subst outcome
    by_cases member : source ∈ locks i
    · have owner : source ∈ group := inside member
      have neverPays : ¬ paid source dir := by
        intro pays
        exact avoid ⟨source, owner, by simp only [shape], pays⟩
      have choice : BlockedPush board (locks i) source dir ∨ Shift board holes locks region i source dir := by
        rcases closed.2 i state.player heroInside dir source member adjacent with blocked | pays | shifted
        · exact Or.inl blocked
        · exact False.elim (neverPays pays)
        · exact Or.inr shifted
      rcases choice with blocked | shifted
      · rcases blocked with diagonal | blocked
        · simp only [first.1] at diagonal
          contradiction
        · obtain ⟨dest, next, floor, door, empty⟩ := first.2
          simp only [next] at blocked
          rcases blocked with wall | door' | box
          · exact False.elim (wall floor)
          · exact False.elim (door door')
          · exact False.elim (empty (actualInside box))
      · obtain ⟨j, dest, destFloor, targets, noHole, nextLocks, nextHero⟩ := shifted
        have landing : result.landing = dest := by simpa only [targets, List.mem_singleton] using spec.2
        have notFilled : result.filled = none := by
          rcases spec.1 with stay | fill
          · exact stay.1
          · exact False.elim (noHole (holesInside (landing ▸ fill.2.1)))
        have erased : (locks i).erase source ⊆ group.erase source :=
          GhostSubset.erase_subset inside (unique i) source
        refine ⟨j, by simpa only [shape] using nextHero, ?_⟩
        simp only [update, move, if_pos owner, ending, notFilled, post]
        rw [landing]
        exact List.Subset.trans nextLocks (List.cons_subset_cons dest erased)
    · have door := FiniteTopology.step_target_not_door board state dir t source adjacent checked
      have targetInside := closed.1 i state.player heroInside dir source adjacent floor door member smallCorner
      have erased : locks i⊆group.erase source := by
        intro cell found
        have different : cell≠source := by intro same; exact member (same ▸ found)
        exact (List.mem_erase_of_ne different).mpr (inside found)
      refine ⟨i,by simpa only [shape] using targetInside,?_⟩
      by_cases owner : source∈group
      · cases filled : result.filled with
        | none =>
          simp only [update,move,if_pos owner,ending,filled,post]
          exact fun _ h => List.mem_cons_of_mem _ (erased h)
        | some hole =>
          simpa only [update,move,if_pos owner,ending,filled,post] using erased
      · simpa only [update,move,if_neg owner] using inside

theorem small_energy_good {n k : Nat} {board : Board} {holes : List Cell}
    {locks region : Fin n → List Cell} {paid : Cell → Dir → Prop}
    (closed : ClosedExcept board holes locks region paid)
    (unique : ∀ i, (locks i).Nodup)
    {invariant : State → Prop} (cert : GroupCertificate board k invariant) (price : Int)
    (priced : ∀ state dir t outcome group,
      invariant state → group.Nodup → group ⊆ state.boulders → group.length ≤ k →
      step board state dir = some t → Matches state t outcome → PaidStep paid group dir t →
      price ≤ charge cert.holeWeight group outcome +
        cert.groupValue t.state (update group outcome) - cert.groupValue state group)
    {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
    (logged : Logged board state dirs final pushes moves outcomes)
    (valid : invariant state) (group : List Cell) (groupUnique : group.Nodup)
    (groupInside : group ⊆ state.boulders) (bounded : group.length ≤ k)
    (good : Good locks region state group) (holesInside : state.holes ⊆ holes)
    (cheap : HeroLedger.energy cert.groupValue cert.holeWeight state final group outcomes < price) :
    Good locks region final (endGroup group outcomes) := by
  induction logged generalizing group with
  | nil current => exact good
  | @cons state dir t rest final pushes moves outcome outcomes head effect tail ih =>
    have nextValid := cert.preserved state dir t valid head
    have nextActual := step_boulders_nodup board state dir t (cert.unique state valid) head
    have nextUnique := GhostSubset.update_unique state t outcome effect nextActual group groupUnique groupInside
    have nextSubset := GhostSubset.update_subset state t outcome effect group groupUnique groupInside
    have nextBound := Nat.le_trans (update_length group outcome) bounded
    have nextHoles := List.Subset.trans (step_holes_sublist board state dir t head).subset holesInside
    have tailNonnegative := HeroLedger.Logged.energy_nonnegative tail cert nextValid
      (update group outcome) nextUnique nextSubset nextBound
    have one := cert.row state dir t outcome group valid groupUnique groupInside bounded head effect
    have decomposition := energy_cons cert.groupValue cert.holeWeight state t.state final group outcome outcomes
    have avoid : ¬ PaidStep paid group dir t := by
      intro pays
      have charged := priced state dir t outcome group valid groupUnique groupInside bounded head effect pays
      omega
    have nextGood := step_good_except closed unique good groupInside holesInside head effect avoid
    have tailCheap : HeroLedger.energy cert.groupValue cert.holeWeight t.state final
        (update group outcome) outcomes < price := by omega
    exact ih nextValid (update group outcome) nextUnique nextSubset nextBound nextGood nextHoles tailCheap


theorem energy_if_empty {n limit : Nat} {board : Board} {holes : List Cell}
 {locks region : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : ClosedExcept board holes locks region paid) (unique : ∀i, (locks i).Nodup)
 (nonempty : ∀i, locks i≠[])
 {invariant : State→Prop} (cert : GroupCertificate board limit invariant) (price : Int)
 (priced : ∀state dir t outcome group, invariant state → group.Nodup → group⊆state.boulders → group.length≤limit →
   step board state dir=some t → Matches state t outcome → PaidStep paid group dir t →
   price≤charge cert.holeWeight group outcome+cert.groupValue t.state (update group outcome)-cert.groupValue state group)
 {state final : State} {dirs : List Dir} {pushes moves : Nat} {outcomes : List Outcome}
 (logged : Logged board state dirs final pushes moves outcomes) (valid : invariant state)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤limit)
 (good : Good locks region state group) (holesInside : state.holes⊆holes)
 (consumed : endGroup group outcomes=[]) :
 price≤HeroLedger.energy cert.groupValue cert.holeWeight state final group outcomes := by
 by_cases enough : price≤HeroLedger.energy cert.groupValue cert.holeWeight state final group outcomes
 · exact enough
 · have cheap : HeroLedger.energy cert.groupValue cert.holeWeight state final group outcomes<price := by omega
   obtain ⟨i,_,selected⟩ := small_energy_good closed unique cert price priced logged valid group groupUnique inside bounded good holesInside cheap
   rw [consumed] at selected
   have empty : locks i=[] := List.eq_nil_iff_forall_not_mem.mpr (by intro c member; simpa using selected member)
   exact False.elim (nonempty i empty)

#print axioms step_good_except
#print axioms energy_if_empty
end Owner1007.OwnedCorralAny11
