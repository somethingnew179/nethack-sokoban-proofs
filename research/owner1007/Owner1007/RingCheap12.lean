import Owner1007.NorthBound12
import Owner1007.RingAfter12
namespace Owner1007.RingCheap12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem guard_check : ∀ hero ∈ RingCut12.region 0, ∀ dir ∈ allDirs, ∀ source ∈ RingCut12.locks 0,
    advance soko1_2.board hero dir = some source →
    BlockedPush soko1_2.board (RingCut12.locks 0) source dir ∨ RingCut12.paid source dir := by
  decide +kernel
theorem guard : ∀ i hero, hero ∈ RingCut12.region i → ∀ dir source, source ∈ RingCut12.locks 0 →
    advance soko1_2.board hero dir = some source →
    BlockedPush soko1_2.board (RingCut12.locks i) source dir ∨ RingCut12.paid source dir := by
  intro i hero inside dir source member adjacent
  have same : i=0 := Subsingleton.elim i 0
  subst i
  exact guard_check hero inside dir (Geometry.all_directions dir) source member adjacent

theorem cheap_activation {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final)
    (hero : state.player ∈ RingCut12.region 0) (inside : RingCut12.locks 0 ⊆ group)
    (cheap : energy p group outcomes ≤ 3) :
    ∃ beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves,
      outcomes = before ++ .push 263 (.stay 262) :: after ∧
      Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before ∧
      step soko1_2.board middle .west = some t ∧ Matches middle t (.push 263 (.stay 262)) ∧
      Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after ∧
      RingCut12.locks 0 ⊆ endGroup group before ∧
      (∀ small : List Cell, small ⊆ RingCut12.locks 0 → endGroup small before = small) := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ RingCut12.matrix
  have initialUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed RingCut12.unique logged reached group unique subset hero inside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,i,shape,first,checked,effect,last,heroBefore,locks,pays,fixed⟩ :=
      event.split_fixed (RingCut12.locks 0) (by intro i; exact fun _ h => h) guard reached unique subset
    have phase : i=0 := Subsingleton.elim i 0
    subst i
    have middleReached := reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have oldGroup := first.end_subset initialUnique group unique subset
    have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
    have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
      (endGroup group before) oldGroup.1 oldGroup.2
    have nextSubset := GhostSubset.update_subset middle t outcome effect
      (endGroup group before) oldGroup.1 oldGroup.2
    have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
    have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
    cases outcome with
    | walk target => exact False.elim pays
    | push source ending =>
      obtain ⟨owner,paid⟩ := pays
      have rawCost := push_effect_price p soko1_2.initial.holes 2
        middleReached.holes_sublist.subset (NorthBound12.ring_priced source dir paid) checked effect
      dsimp only [p] at *
      rcases paid with h | h | h | h
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 210 .south = [236] by decide +kernel) (by decide +kernel) checked effect
        subst ending
        have erased := GhostSubset.erase_subset locks (RingCut12.unique 0) 210
        have newInside : RingAfter12.locks false 0 ⊆ update (endGroup group before) (.push 210 (.stay 236)) := by
          simp only [update,move,if_pos owner,post]
          have shifted : RingAfter12.locks false 0 ⊆ 236 :: (RingCut12.locks 0).erase 210 := by decide +kernel
          exact List.Subset.trans shifted (List.cons_subset_cons 236 erased)
        have newHero : t.state.player ∈ RingAfter12.region false 0 := by
          rw [matches_hero middle t (.push 210 (.stay 236)) effect]
          decide +kernel
        have later := RingAfter12.owned_energy_two false last nextReached
          (update (endGroup group before) (.push 210 (.stay 236))) nextUnique nextSubset completed newHero newInside
        simp only [RingAfter12.p] at later
        rw [shape,energy_at_split] at cheap
        simp only [projectedOutcome,if_pos owner] at cheap
        omega
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 237 .west = [236] by decide +kernel) (by decide +kernel) checked effect
        subst ending
        have erased := GhostSubset.erase_subset locks (RingCut12.unique 0) 237
        have newInside : [210,236] ⊆ update (endGroup group before) (.push 237 (.stay 236)) := by
          simp only [update,move,if_pos owner,post]
          have shifted : ([210,236] : List Cell) ⊆ 236 :: (RingCut12.locks 0).erase 237 := by decide +kernel
          exact List.Subset.trans shifted (List.cons_subset_cons 236 erased)
        have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
          (update (endGroup group before) (.push 237 (.stay 236))) nextUnique nextSubset
          [210,236] RingAfter12.locked_pair (by decide +kernel) newInside
        have high : (2 : Int) ≤ debtOf p [210,236] := by decide +kernel
        dsimp only [p] at high
        rw [shape,energy_at_split] at cheap
        simp only [projectedOutcome,if_pos owner] at cheap
        omega
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 263 .west = [262] by decide +kernel) (by decide +kernel) checked effect
        subst ending
        exact ⟨beforeDirs,beforePushes,beforeMoves,before,middle,t,after,afterDirs,afterPushes,afterMoves,
          shape,first,checked,effect,last,locks,fixed⟩
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 290 .west = [289] by decide +kernel) (by decide +kernel) checked effect
        subst ending
        have erased := GhostSubset.erase_subset locks (RingCut12.unique 0) 290
        have newInside : RingAfter12.locks true 0 ⊆ update (endGroup group before) (.push 290 (.stay 289)) := by
          simp only [update,move,if_pos owner,post]
          have shifted : RingAfter12.locks true 0 ⊆ 289 :: (RingCut12.locks 0).erase 290 := by decide +kernel
          exact List.Subset.trans shifted (List.cons_subset_cons 289 erased)
        have newHero : t.state.player ∈ RingAfter12.region true 0 := by
          rw [matches_hero middle t (.push 290 (.stay 289)) effect]
          decide +kernel
        have later := RingAfter12.owned_energy_two true last nextReached
          (update (endGroup group before) (.push 290 (.stay 289))) nextUnique nextSubset completed newHero newInside
        simp only [RingAfter12.p] at later
        rw [shape,energy_at_split] at cheap
        simp only [projectedOutcome,if_pos owner] at cheap
        omega
  · obtain ⟨i,hero,locks⟩ := terminal
    have finalInside := logged.end_subset initialUnique group unique subset
    have count := List.Nodup.length_le_of_subset (RingCut12.unique i) (List.Subset.trans locks finalInside.2)
    have large := RingCut12.size i
    have reachedFinal := reached.append logged.trace
    have conserved := reachedFinal.conservation
    have empty : final.holes=[] := completed
    change 20 + final.holes.length = final.boulders.length + 18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega
#print axioms cheap_activation
end Owner1007.RingCheap12
