import Owner1007.After238210Bound12
import Owner1007.Park317Cash12
namespace Owner1007.After238210Park12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.After23821012
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem cash_cases_strong {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (completed : Goal final)
    (group : List Cell) (gUnique : group.Nodup) (gSubset : group ⊆ state.boulders)
    (i : Fin 5) (hero : state.player ∈ region i) (inside : locks i ⊆ group) :
    2≤energy p ordinary outcomes ∨ 4≤energy p group outcomes := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed unique logged reached group gUnique gSubset hero inside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroOne,locksOne,pays,unchanged⟩ :=
      event.split_fixed fixed fixed_inside fixed_guard reached gUnique gSubset
    have middleReached := reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have oldInside := first.end_subset actualUnique group gUnique gSubset
    have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
    have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
      (endGroup group before) oldInside.1 oldInside.2
    have nextSubset := GhostSubset.update_subset middle t outcome effect
      (endGroup group before) oldInside.1 oldInside.2
    have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
    cases outcome with
    | walk target => exact False.elim pays
    | push source ending =>
      obtain ⟨owner,paid⟩ := pays
      have rawCost := push_effect_price p soko1_2.initial.holes (if source=318 then (3:Int) else 2)
        middleReached.holes_sublist.subset (priced_min paid) checked effect
      have allBound := event_energy_le Generated.soko1_2_potential_valid group first last (.push source ending)
      simp only [projectedOutcome,if_pos owner] at allBound
      change slack p (.push source ending) ≤ energy p group (before ++ .push source ending :: after) at allBound
      rcases paid with h | h | h
      · obtain ⟨choices,direction⟩ := h
        have member : source∈ordinary := by rcases choices with rfl | rfl | rfl <;> decide +kernel
        have prior := unchanged ordinary (by intro c h; exact List.mem_append_left _ h)
        have bound := event_energy_le Generated.soko1_2_potential_valid ordinary first last (.push source ending)
        simp only [prior,projectedOutcome,if_pos member] at bound
        change slack p (.push source ending) ≤ energy p ordinary (before ++ .push source ending :: after) at bound
        have different : source≠318 := by intro same; subst source; contradiction
        have two : (2:Int)≤slack p (.push source ending) := by simpa only [if_neg different] using rawCost
        exact Or.inl (by rw [shape]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
          (by decide +kernel) checked effect
        subst ending
        have currentMember : NorthEvents12.current j∈Park317Cash12.northCells := by
          have check : ∀ k : Fin 5, NorthEvents12.current k∈Park317Cash12.northCells := by decide +kernel
          exact check j
        have currentInside : NorthEvents12.current j∈endGroup group before := by
          apply locksOne
          have check : ∀ k : Fin 5, NorthEvents12.current k∈After23821012.locks k := by decide +kernel
          exact check j
        have five := Park317Cash12.group_five first checked effect last reached group gUnique gSubset
          (NorthEvents12.current j) currentMember owner currentInside
        change 5≤energy p group (before++(.push 318 (.stay 317))::after) at five
        exact Or.inr (by rw[shape];omega)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          NorthEvents12.ring_activation (by decide +kernel) checked effect
        subst ending
        have erased := GhostSubset.erase_subset locksOne (unique j) 291
        have activation : ∀ j, AfterJ12.ringLocks 0 0 ⊆ 290::(locks j).erase 291 := by decide +kernel
        have ringInside : AfterJ12.ringLocks 0 0 ⊆ update (endGroup group before) (.push 291 (.stay 290)) := by
          simp only [update,move,if_pos owner,post]
          exact List.Subset.trans (activation j) (List.cons_subset_cons 290 erased)
        have heroNext : t.state.player=291 := matches_hero middle t (.push 291 (.stay 290)) effect
        have ringHeroNext : t.state.player∈AfterJ12.ringRegion 0 0 := by rw [heroNext]; exact AfterJ12.ringHero 0
        have ringClosed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ (AfterJ12.ringMatrix 0)
        have later := closedExcept_energy ringClosed (AfterJ12.ringUnique 0) (AfterJ12.ringLarge 0) 2 (AfterJBound12.ring_priced 0)
          last nextReached (update (endGroup group before) (.push 291 (.stay 290)))
          nextUnique nextSubset completed ringHeroNext ringInside
        change 2≤energy p (update (endGroup group before) (.push 291 (.stay 290))) after at later
        have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
        change 0≤ownSlack p group before at prefixNN
        have two : (2:Int)≤slack p (.push 291 (.stay 290)) := by simpa using rawCost
        exact Or.inr (by rw [shape,energy_at_split]; simp only [projectedOutcome,if_pos owner]; omega)
  · obtain ⟨j,hero,locksInside⟩ := terminal
    have endInside := logged.end_subset actualUnique group gUnique gSubset
    have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksInside endInside.2)
    have large := size j
    have conserved := (reached.append logged.trace).conservation
    have empty : final.holes=[] := completed
    change 20+final.holes.length=final.boulders.length+18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega
#print axioms cash_cases_strong
end Owner1007.After238210Park12

