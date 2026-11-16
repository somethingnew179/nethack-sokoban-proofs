import Owner1007.After29012

namespace Owner1007.After29012
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem energy_six
 (matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true)
 (classification : ∀ (i : Fin 4) (hero : Cell), hero∈region i → ∀ dir source, source∈sources → advance soko1_2.board hero dir=some source → paid source dir → classified i source dir)
 {state final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board state dirs final pushes moves outcomes)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) {i : Fin 4}
 (hero : state.player∈region i) (inside : locks i⊆group) :
 6≤energy p group outcomes := by
 have closed := PricedCorral11.closed_of_checkExcept _ _ _ _ _ matrix
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 rcases event_or_good closed unique logged reached group gUnique subset hero inside with event|terminal
 · obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,dir,t,outcome,after,
     afterDirs,afterPushes,afterMoves,j,shape,first,checked,effect,last,heroBefore,locksOne,pays⟩ := event.split
   have middleReached := reached.append first.trace
   have middleUnique := middleReached.boulders_nodup (by decide +kernel)
   have oldGroup := first.end_subset actualUnique group gUnique subset
   have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
   have nextUnique := GhostSubset.update_unique middle t outcome effect nextActual
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextSubset := GhostSubset.update_subset middle t outcome effect
     (endGroup group before) oldGroup.1 oldGroup.2
   have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
   have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
   change 0≤ownSlack p group before at prefixNN
   cases outcome with
   | walk target => exact False.elim pays
   | push source ending =>
     obtain ⟨owner,pays⟩ := pays
     obtain ⟨result,adjacent,push⟩ := effect_push_data checked effect
     have cases := classification j middle.player heroBefore dir source (sources_paid source dir pays) adjacent pays
     have oneNN := logged_step_slack_nonnegative Generated.soko1_2_potential_valid checked effect
     have keep (dest : Cell) (small : List Cell) (smallShift : small⊆dest::(locks j).erase source) :
        small⊆update (endGroup group before) (.push source (.stay dest)) :=
       CageFour12.shifted_inside (unique j) locksOne owner smallShift
     have reserve (a b : Int) (one : a≤slack p (.push source ending))
       (later : b≤energy p (update (endGroup group before) (.push source ending)) after) :
       a+b≤energy p group outcomes := by
       rw [shape,energy_at_split]
       simp only [projectedOutcome,if_pos owner]
       omega

     rcases cases with blocked | main | upper | square | foreign | high
     · exact False.elim (CageFour12.blocked_impossible (List.Subset.trans locksOne oldGroup.2) checked effect blocked)
     · obtain ⟨rfl,rfl⟩ := main
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 263 .west=[262] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have kept := keep 262 (Cage10.locks (cageIndex j)) (cage_activation j)
       have heroNext : t.state.player∈Cage10.region (cageIndex j) := by
         rw [matches_hero middle t (.push 263 (.stay 262)) effect]
         exact cage_hero j
       have later := CageFour12.energy_four last nextReached
         (update (endGroup group before) (.push 263 (.stay 262))) nextUnique nextSubset completed heroNext kept
       change 4≤energy p (update (endGroup group before) (.push 263 (.stay 262))) after at later
       have one : (2:Int)≤slack p (.push 263 (.stay 262)) := by decide +kernel
       exact reserve 2 4 one later
     · obtain ⟨rfl,rfl,pairBefore⟩ := upper
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         (show pushTargets soko1_2.board 187 .north=[161] by decide +kernel)
         (by decide +kernel) checked effect
       subst ending
       have pairInside := keep 161 [186,212] (upper_after187 j pairBefore)
       have ringInside := keep 161 (RingAfter12.locks true 0) (ring_after187 j)
       have heroRing : t.state.player∈TwoReserves12.region true := by
         rw [matches_hero middle t (.push 187 (.stay 161)) effect]
         decide +kernel
       have heroPair : t.state.player∈VerticalPair12.region false 0 := by
         rw [matches_hero middle t (.push 187 (.stay 161)) effect]
         decide +kernel
       have later := TwoReserves12.pair_ring_four false true last nextReached
         (update (endGroup group before) (.push 187 (.stay 161))) nextUnique nextSubset completed
         heroRing heroPair pairInside ringInside
       change 4≤energy p (update (endGroup group before) (.push 187 (.stay 161))) after at later
       have one : (2:Int)≤slack p (.push 187 (.stay 161)) := by decide +kernel
       exact reserve 2 4 one later
     · obtain ⟨which,square⟩ := square
       have targets : pushTargets soko1_2.board source dir=[squareDest source] := by
         rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
       have clear : squareDest source∉soko1_2.initial.holes := by
         rcases which with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel
       have endingSame := push_effect_singleton soko1_2.initial.holes middleReached.holes_sublist.subset
         targets clear checked effect
       subst ending
       have kept := keep (squareDest source) [186,187,212,213] square
       have later := last.locked_group_energy Generated.soko1_2_potential_valid nextActual
         (update (endGroup group before) (.push source (.stay (squareDest source)))) nextUnique nextSubset
         [186,187,212,213] CageLedger12.locked_middle_square (by decide +kernel) kept
       change debtOf p [186,187,212,213]≤energy p (update (endGroup group before) (.push source (.stay (squareDest source)))) after at later
       have bound := reserve 0 (debtOf p [186,187,212,213]) oneNN later
       have amount : (6:Int)≤debtOf p [186,187,212,213] := by decide +kernel
       omega
     · obtain ⟨notUpper,notRing,priced⟩ := foreign
       have upperBefore := List.Subset.trans (upperInside j) locksOne
       have upperAfter := update_mono CageLedger12.Upper (endGroup group before)
         (by decide +kernel) upperBefore (.push source ending)
       simp only [update,move,if_neg notUpper] at upperAfter
       have ringBefore := List.Subset.trans (ringInside j) locksOne
       have ringAfter := update_mono (RingAfter12.locks true 0) (endGroup group before)
         (by decide +kernel) ringBefore (.push source ending)
       simp only [update,move,if_neg notRing] at ringAfter
       have heroRing : t.state.player∈TwoReserves12.region true := by
         rw [matches_hero middle t (.push source ending) effect]
         exact ring_hero source (sources_paid source dir pays) notUpper notRing
       have bonus : RightEnergy12.cert.bonus t.state.player
         (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by
         rw [matches_hero middle t (.push source ending) effect]
         exact upper_bonus source (sources_paid source dir pays) notUpper
       have later := TwoReserves12.upper_ring_four true last nextReached
         (update (endGroup group before) (.push source ending)) nextUnique nextSubset completed
         heroRing bonus upperAfter ringAfter
       change 4≤energy p (update (endGroup group before) (.push source ending)) after at later
       have one := push_effect_price p soko1_2.initial.holes 2 middleReached.holes_sublist.subset priced checked effect
       exact reserve 2 4 one later
     · obtain ⟨notUpper,priced⟩ := high
       have upperBefore := List.Subset.trans (upperInside j) locksOne
       have upperAfter := update_mono CageLedger12.Upper (endGroup group before)
         (by decide +kernel) upperBefore (.push source ending)
       simp only [update,move,if_neg notUpper] at upperAfter
       have upperActual := List.Subset.trans upperAfter nextSubset
       have bonus : RightEnergy12.cert.bonus t.state.player
         (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by
         rw [matches_hero middle t (.push source ending) effect]
         exact upper_bonus source (sources_paid source dir pays) notUpper
       have upperBound := RightEnergy12.raw_group_energy last nextReached CageLedger12.Upper
         (by decide +kernel) upperActual completed
       rw [bonus] at upperBound
       change 2≤energy p CageLedger12.Upper after at upperBound
       have mono := last.energy_mono Generated.soko1_2_potential_valid nextActual
         CageLedger12.Upper (update (endGroup group before) (.push source ending))
         (by decide +kernel) nextUnique upperActual nextSubset upperAfter
       have later : (2:Int)≤energy p (update (endGroup group before) (.push source ending)) after := Int.le_trans upperBound mono
       have one := push_effect_price p soko1_2.initial.holes 4 middleReached.holes_sublist.subset priced checked effect
       exact reserve 4 2 one later
 · obtain ⟨j,hero,locksOne⟩ := terminal
   have finalInside := logged.end_subset actualUnique group gUnique subset
   have count := List.Nodup.length_le_of_subset (unique j) (List.Subset.trans locksOne finalInside.2)
   have size : ∀ j, (locks j).length=12 := by decide +kernel
   rw [size j] at count
   have conserved := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   change 20+final.holes.length=final.boulders.length+18 at conserved
   rw [empty] at conserved
   simp only [List.length_nil] at conserved
   omega
#print axioms energy_six
end Owner1007.After29012

