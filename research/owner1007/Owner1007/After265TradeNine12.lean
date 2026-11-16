import Owner1007.After265PureEight12
import Owner1007.After265EastTrade12
namespace Owner1007.After265TradeNine12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.After265PureEight12 (p no_west keep291)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem east_activation:∀i:Fin 4,∀j:Fin 19,i.val=j.val→i.val<3→
 After265EastTrade12.locks j⊆292::(After26512.locks i).erase 291∧
 291∈After265EastTrade12.region j∧7≤After265EastTrade12.credit j:=by decide +kernel
theorem energy_nine_or_two {state final dirs pushes moves outcomes}
    (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
    {history : List Dir} {past pastMoves : Nat}
    (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
    (group : List Cell) (unique : group.Nodup) (subset : group ⊆ state.boulders)
    (completed : Goal final) {i : Fin 4}
    (hero : state.player ∈ After26512.region i) (inside : After26512.locks i ⊆ group) :
    9≤energy p group outcomes∨(8≤energy p group outcomes∧2≤(endGroup group outcomes).length):=by
  have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ After26512.matrix
  have eight:=After265PureEight12.energy_eight logged reached group unique subset completed hero inside
  have actualUnique := reached.boulders_nodup (by decide +kernel)
  rcases event_or_good closed After26512.unique logged reached group unique subset hero inside with event | terminal
  · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
      afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locks,pays⟩ := event.split
    have middleReached := reached.append first.trace
    have middleUnique := middleReached.boulders_nodup (by decide +kernel)
    have oldGroup := first.end_subset actualUnique group unique subset
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
      obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
      have reserve (a b : Int) (one : a ≤ slack p (.push source ending))
          (later : b ≤ energy p (update (endGroup group before) (.push source ending)) after) :
          a+b ≤ energy p group outcomes := by
        rw [shape,energy_at_split]
        simp only [projectedOutcome,if_pos owner]
        change 0 ≤ ownSlack p group before at prefixNN
        omega
      rcases paid with ⟨rfl,dircases⟩ | ⟨rfl,rfl⟩
      · rcases dircases with rfl | rfl | rfl
        · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            (show pushTargets soko1_2.board 291 .east=[292] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have actualInside := List.Subset.trans locks oldGroup.2
          obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear soko1_2.board middle 291 .east result push).2
          have destEq : dest=292 := Option.some.inj (next.symm.trans (by decide +kernel))
          have clear292 : 292 ∉ middle.boulders := by simpa only [destEq] using clear
          have small : j.val<3 := by
            by_cases yes : j.val<3
            · exact yes
            · have val : j.val=3 := by have h:=j.isLt; omega
              have same : j=(3:Fin 4) := Fin.ext val
              subst j
              exact False.elim (clear292 (actualInside (by decide +kernel)))
          let b:Fin 19:=⟨j.val,by omega⟩
          obtain⟨shift,newHero,credit⟩:=east_activation j b rfl small
          have kept:=CageFour12.shifted_inside (After26512.unique j) locks owner shift
          have heroNext:t.state.player∈After265EastTrade12.region b:=by
            rw[matches_hero middle t (.push 291 (.stay 292)) effect]
            exact newHero
          have later:=After265EastTrade12.owned_trade last nextReached
            (update (endGroup group before) (.push 291 (.stay 292))) nextUnique nextSubset b heroNext kept
          rcases later with high|two
          ·change After265EastTrade12.credit b≤energy p (update (endGroup group before) (.push 291 (.stay 292))) after at high
           have laterSeven:7≤energy p (update (endGroup group before) (.push 291 (.stay 292))) after:=by omega
           have bound:=reserve 2 7 (by decide +kernel) laterSeven
           exact Or.inl (by omega)
          ·have length:2≤(endGroup group outcomes).length:=by
            rw[shape,endGroup_append]
            exact two
           exact Or.inr ⟨eight,length⟩
        · exact False.elim (no_west j middle.player heroBefore adjacent)
        · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
            (show pushTargets soko1_2.board 291 .south=[317] by decide +kernel)
            (by decide +kernel) checked effect
          subst ending
          have shift : ∀j:Fin 4,([317,318]:List Cell)⊆317::(After26512.locks j).erase 291 := by decide +kernel
          have kept:=CageFour12.shifted_inside (After26512.unique j) locks owner (shift j)
          have later:=last.locked_group_energy Generated.soko1_2_potential_valid nextActual
            (update (endGroup group before) (.push 291 (.stay 317))) nextUnique nextSubset
            [317,318] (locked_of_check _ _ (by decide +kernel)) (by decide +kernel) kept
          have debt : debtOf p [317,318]=2 := by decide +kernel
          rw[debt] at later
          have bound := reserve 7 2 (by decide +kernel) later
          exact (by omega)
      · have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
          (show pushTargets soko1_2.board 318 .west=[317] by decide +kernel)
          (by decide +kernel) checked effect
        subst ending
        have nextShape : t.state.boulders=317::middle.boulders.erase 318 := by
          simpa only [Matches] using congrArg (fun x : Transition=>x.state.boulders) effect.2
        have present : 317 ∈ t.state.boulders := by rw [nextShape]; simp
        have survives := DeadCorridor12.trapped_survives last present nextReached.holes_sublist.subset
          291 (by decide +kernel)
        have ledger := survivor_energy p 291 after survives
        have nn : (0:Int) ≤ (ownPushes [291] after : Int) := Int.natCast_nonneg _
        have single : (6:Int) ≤ energy p [291] after := by
          have debt : -p.boulder 291=6 := by decide +kernel
          rw [debt] at ledger
          simp only [Int.ofNat_eq_natCast] at ledger
          omega
        have kept := CageFour12.shifted_inside (After26512.unique j) locks owner (keep291 j)
        have aActual := List.Subset.trans kept nextSubset
        have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual [291]
          (update (endGroup group before) (.push 318 (.stay 317)))
          (by decide +kernel) nextUnique aActual nextSubset kept
        change energy p [291] after ≤ energy p (update (endGroup group before) (.push 318 (.stay 317))) after at mono
        have later : 6 ≤ energy p (update (endGroup group before) (.push 318 (.stay 317))) after := by omega
        have bound := reserve 3 6 (by decide +kernel) later
        exact (by omega)
  · obtain ⟨j,_,kept⟩ := terminal
    have finalInside := logged.end_subset actualUnique group unique subset
    have count := List.Nodup.length_le_of_subset (After26512.unique j) (List.Subset.trans kept finalInside.2)
    have size := After26512.size j
    have conserved := (reached.append logged.trace).conservation
    have empty : final.holes=[] := completed
    change 20 + final.holes.length = final.boulders.length + 18 at conserved
    rw [empty] at conserved
    simp only [List.length_nil] at conserved
    omega
#print axioms energy_nine_or_two
end Owner1007.After265TradeNine12
