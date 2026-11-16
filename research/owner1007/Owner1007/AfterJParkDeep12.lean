import Owner1007.AfterJParkRecursive12
import Owner1007.AfterJDeep12
import Owner1007.AfterJSurvivalRecursive12
import Owner1007.AfterJSurvivalLate12
namespace Owner1007.AfterJParkDeep12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.AfterJ12
open Owner1007.AfterJBound12 (matrices priced_min)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem cash_cases_strong {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (completed : Goal final) (kind : Fin 2)
    (group : List Cell) (gUnique : group.Nodup) (gSubset : group ⊆ state.boulders)
    (i : Fin 5) (hero : state.player ∈ region kind i) (inside : locks kind i ⊆ group) :
    4≤energy p (ordinary kind) outcomes ∨ 6≤energy p group outcomes := by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ (matrices kind)
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed (unique kind) logged reached group gUnique gSubset hero inside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroOne,locksOne,pays,unchanged⟩ :=
      event.split_fixed (fixed kind) (fixed_inside kind) (fixed_guard kind) reached gUnique gSubset
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
      have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
      change 0≤ownSlack p group before at prefixNN
      rcases paid with h | h | h
      · obtain ⟨member,direction⟩ := h
        have prior := unchanged (ordinary kind) (fun _ h=>List.mem_append_left _ h)
        have bound := event_energy_le Generated.soko1_2_potential_valid (ordinary kind) first last (.push source ending)
        simp only [prior,projectedOutcome,if_pos member] at bound
        change slack p (.push source ending)≤energy p (ordinary kind) (before++ .push source ending::after) at bound
        rcases direction with ⟨choices,directionEq⟩ | ⟨rfl,directionEq⟩
        · rcases choices with rfl|rfl|rfl|rfl|rfl
          · have kindEq : kind=(1:Fin 2) :=
              (show ∀ kind : Fin 2, (210:Cell)∈ordinary kind → kind=1 from by decide +kernel) kind member
            subst kind
            have checkedSouth : step soko1_2.board middle .south=some t := by simpa only [directionEq] using checked
            have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 210 .south=[236] by decide +kernel)
              (by decide +kernel) checkedSouth effect
            subst ending
            have deep := AfterJParkRecursive12.after210 first checkedSouth effect last reached
              group gUnique gSubset j locksOne prior completed
            change 4≤energy p (ordinary 1) (before++(.push 210 (.stay 236))::after) ∨
              6≤energy p group (before++(.push 210 (.stay 236))::after) at deep

            simpa only [shape] using deep
          · have kindEq : kind=(0:Fin 2) :=
              (show ∀ kind : Fin 2, (236:Cell)∈ordinary kind → kind=0 from by decide +kernel) kind member
            subst kind
            have checkedSouth : step soko1_2.board middle .south=some t := by simpa only [directionEq] using checked
            have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 236 .south=[262] by decide +kernel)
              (by decide +kernel) checkedSouth effect
            subst ending
            have deep := AfterJParkRecursive12.after236 first checkedSouth effect last reached
              group gUnique gSubset j locksOne prior completed
            change 4≤energy p (ordinary 0) (before++(.push 236 (.stay 262))::after) ∨
              6≤energy p group (before++(.push 236 (.stay 262))::after) at deep

            simpa only [shape] using deep
          · have kindEq : kind=(0:Fin 2) :=
              (show ∀ kind : Fin 2, (238:Cell)∈ordinary kind → kind=0 from by decide +kernel) kind member
            subst kind
            have checkedSouth : step soko1_2.board middle .south=some t := by simpa only [directionEq] using checked
            have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 238 .south=[264] by decide +kernel)
              (by decide +kernel) checkedSouth effect
            subst ending
            have deep := AfterJParkRecursive12.after238 first checkedSouth effect last reached
              group gUnique gSubset j locksOne prior completed
            change 4≤energy p (ordinary 0) (before++(.push 238 (.stay 264))::after) ∨
              6≤energy p group (before++(.push 238 (.stay 264))::after) at deep

            simpa only [shape] using deep
          · have kindEq : kind=(1:Fin 2) :=
              (show ∀ kind : Fin 2, (264:Cell)∈ordinary kind → kind=1 from by decide +kernel) kind member
            subst kind
            have checkedSouth : step soko1_2.board middle .south=some t := by simpa only [directionEq] using checked
            have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 264 .south=[290] by decide +kernel)
              (by decide +kernel) checkedSouth effect
            subst ending
            have price : slack p (.push 264 (.stay 290))=4 := by decide +kernel
            rw [price] at bound
            exact Or.inl (by rw [shape]; exact bound)
          · have checkedSouth : step soko1_2.board middle .south=some t := by simpa only [directionEq] using checked
            have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 265 .south=[291] by decide +kernel)
              (by decide +kernel) checkedSouth effect
            subst ending
            have deep := AfterJDeepLeaves12.after265_seven first checkedSouth effect last reached
              group gUnique gSubset kind j locksOne completed
            have enough : 6≤energy p group (before++(.push 265 (.stay 291))::after) := by
              change 7≤energy p group (before++(.push 265 (.stay 291))::after) at deep
              omega
            exact Or.inr (by rw [shape]; exact enough)
        · obtain ⟨k,small⟩ := kind
          have kinds : k=0∨k=1 := by omega
          rcases kinds with rfl|rfl
          · have impossible : ∀ j : Fin 5, BlockedPush soko1_2.board (locks 0 j) 237 .west := by decide +kernel
            have checkedWest : step soko1_2.board middle .west=some t := by simpa only [directionEq] using checked
            exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldInside.2)
              checkedWest effect (impossible j))
          · have checkedWest : step soko1_2.board middle .west=some t := by simpa only [directionEq] using checked
            have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
              (show pushTargets soko1_2.board 237 .west=[236] by decide +kernel)
              (by decide +kernel) checkedWest effect
            subst ending
            have activation : ∀ j : Fin 5, ([210,236] : List Cell)⊆236::(locks 1 j).erase 237 := by decide +kernel
            have kept := CageFour12.shifted_inside (unique 1 j) locksOne owner (activation j)
            have future := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
              (update (endGroup group before) (.push 237 (.stay 236))) nextUnique nextSubset
              [210,236] RingAfter12.locked_pair (by decide +kernel) kept
            change 15≤energy p (update (endGroup group before) (.push 237 (.stay 236))) after at future
            have price : slack p (.push 237 (.stay 236))=2 := by decide +kernel
            exact Or.inr (by rw [shape,energy_at_split]; simp only [projectedOutcome,if_pos owner,price]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
          (by decide +kernel) checked effect
        subst ending
        have deep := AfterJDeepLate12.after318_seven first checked effect last reached
          group gUnique gSubset kind j locksOne owner heroOne completed
        change 7≤energy p group (before++(.push 318 (.stay 317))::after) at deep
        exact Or.inr (by rw [shape]; omega)
      · obtain ⟨rfl,rfl⟩ := h
        have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          NorthEvents12.ring_activation (by decide +kernel) checked effect
        subst ending
        have deep := AfterJSurvivalLate12.after291_six first checked effect last reached
          group gUnique gSubset kind j locksOne owner heroOne completed
        change 6≤energy p group (before++(.push 291 (.stay 290))::after) at deep
        exact Or.inr (by rw [shape]; exact deep)

  · obtain ⟨j,hero,locksInside⟩ := terminal
    have endInside := logged.end_subset actualUnique group gUnique gSubset
    have count := List.Nodup.length_le_of_subset (unique kind j) (List.Subset.trans locksInside endInside.2)
    have large := size kind j
    have conserved := (reached.append logged.trace).conservation
    have empty : final.holes=[] := completed
    change 20+final.holes.length=final.boulders.length+18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega

#print axioms cash_cases_strong
end Owner1007.AfterJParkDeep12

