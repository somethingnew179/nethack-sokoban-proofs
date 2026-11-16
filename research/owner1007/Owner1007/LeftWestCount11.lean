import Owner1007.PaidCount11
import Owner1007.LeftEnergy11
import Owner1007.PairFirstCut11
import NetHack.Sokoban.Reduction
namespace Owner1007.LeftWestCount11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem find {n : Nat} {locks region : Fin n→List Cell} {paid : Cell→Dir→Prop}
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (uniqueLocks : ∀i,(locks i).Nodup) (sizeLocks : ∀i,(locks i).length=2)
 {prior state dirs final pushes moves outcomes priorPushes priorMoves}
 (reached : Trace soko1_1.board soko1_1.initial prior state priorPushes priorMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤2)
 (good : OwnedCorral11.Good locks region state group) (consumed : endGroup group outcomes=[]) :
 Nonempty (FirstCut paid state group dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet logged group with found|quiet
 · exact found
 · have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   obtain ⟨i,_,selected⟩ := PairFirstCut11.quiet_good closed uniqueLocks sizeLocks quiet valid.1 unique inside bounded good reached.holes_sublist.subset
   have card := List.Nodup.length_le_of_subset (uniqueLocks i) selected
   rw [sizeLocks i,consumed] at card
   simp at card
theorem two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (consumed : endGroup [186,212] outcomes=[]) :
 2≤PaidCount11.count LeftPair11.paid [186,212] dirs outcomes := by
 have good : OwnedCorral11.Good LeftPair11.cut0Locks LeftPair11.cut0Region soko1_1.initial [186,212] := by
   refine ⟨0,?_,?_⟩ <;> decide +kernel
 obtain ⟨first⟩ := find LeftPair11.first_closed LeftEnergy11.first_unique LeftEnergy11.first_size
   (Trace.nil soko1_1.initial) logged [186,212] (by decide) (by decide) (by decide) good consumed
 have beforeGood := PairFirstCut11.quiet_good LeftPair11.first_closed LeftEnergy11.first_unique LeftEnergy11.first_size
   first.before (by decide) (by decide) (by decide) (by decide) good (by simp)
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.before.logged.trace
 have selected := first.before.logged.end_subset (by decide) [186,212] (by decide) (by decide)
 have bound := endGroup_length_le [186,212] first.beforeOutcomes
 have afterGood := (LeftEnergy11.after_first valid first.headChecked first.headEffect selected.1 bound beforeGood first.headPaid).1
 have actual := step_boulders_nodup _ _ _ _ valid.1 first.headChecked
 let group := update (endGroup [186,212] first.beforeOutcomes) first.headOutcome
 have unique := GhostSubset.update_unique _ _ _ first.headEffect actual _ selected.1 selected.2
 have inside := GhostSubset.update_subset _ _ _ first.headEffect _ selected.1 selected.2
 have bounded : group.length≤2 := Nat.le_trans (update_length _ _) bound
 have reached := first.before.logged.trace.append (Trace.cons first.headChecked (Trace.nil first.actor.state))
 have gone : endGroup group first.afterOutcomes=[] := by
   rw [first.outcomesEq,endGroup_append] at consumed
   exact consumed
 obtain ⟨second⟩ := find LeftPair11.closed LeftPair11.unique LeftPair11.size reached first.after group unique inside bounded afterGood gone
 have secondBound := PaidCount11.event_le (paid:=LeftPair11.paid) (lastDirs:=second.afterDirs) (last:=second.afterOutcomes) second.before.logged second.headEffect group second.headPaid
 have afterCount : 1≤PaidCount11.count LeftPair11.paid group first.afterDirs first.afterOutcomes := by
   rw [←second.dirsEq,←second.outcomesEq] at secondBound
   omega
 have firstPaid : OwnedCorral11.PaidStep LeftPair11.paid (endGroup [186,212] first.beforeOutcomes) first.direction first.actor := by
   obtain ⟨source,owner,metadata,sources,west⟩ := first.headPaid
   refine ⟨source,owner,metadata,?_⟩
   rcases sources with rfl|rfl <;> simp [LeftPair11.paid,west]
 have firstBound := PaidCount11.event_le (paid:=LeftPair11.paid) (lastDirs:=first.afterDirs) (last:=first.afterOutcomes) first.before.logged first.headEffect [186,212] firstPaid
 rw [←first.dirsEq,←first.outcomesEq] at firstBound
 change 1+PaidCount11.count LeftPair11.paid group first.afterDirs first.afterOutcomes≤PaidCount11.count LeftPair11.paid [186,212] dirs outcomes at firstBound
 omega
#print axioms two
end Owner1007.LeftWestCount11