import Owner1007.AboveOther11
import Owner1007.OtherTrap31811
import Owner1007.QuietGroupFixed11
import Owner1007.TransportQuiet11
import Owner1007.CentralFirst11Proof
namespace Owner1007.AboveOtherZero11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.ModeC264Mass11 (Other)
open Owner1007.AboveOther11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem find {history state past pastMoves dirs final pushes moves outcomes}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (inside : locks 0⊆state.boulders) (good : OwnedCorral11.Good locks region state (locks 0)) :
 Nonempty (FirstCut paid state (locks 0) dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet (paid:=paid) logged (locks 0) with found|quiet
 ·exact found
 ·have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
  obtain ⟨i,_,selected⟩ := PairFirstCut11.quiet_good closed unique size quiet valid.1 (unique 0) inside (by decide) good reached.holes_sublist.subset
  have actual := (logged.end_subset valid.1 (locks 0) (unique 0) inside).2
  have card := List.Nodup.length_le_of_subset (unique i) (List.Subset.trans selected actual)
  rw [size i] at card
  have conservation := (reached.append logged.trace).conservation
  have empty : final.holes=[] := completed
  rw [empty] at conservation
  change 18+0=final.boulders.length+16 at conservation
  omega

theorem impossible {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (zero : energy soko1_1.initial final Other (before++outcomes)=0)
 (owns : G⊆endGroup Other before) (front : 265∈state.boulders) (hero : state.player=239) : False := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have currentOther := first.end_subset (by decide) Other (by decide) (by decide)
 have gInside : G⊆state.boulders := List.Subset.trans owns currentOther.2
 have jointInside : locks 0⊆state.boulders := by
  change G++[265]⊆state.boulders
  exact List.append_subset.mpr ⟨gInside,by simpa using front⟩
 have good : OwnedCorral11.Good locks region state (locks 0) := ⟨0,by rw [hero];decide +kernel,fun _ h=>h⟩
 obtain ⟨cut⟩ := find first.trace logged completed jointInside good
 obtain ⟨i,heroInside,locksInside⟩ := PairFirstCut11.quiet_good closed unique size cut.before valid.1 (unique 0) jointInside (by decide) good first.trace.holes_sublist.subset
 have jointFacts := cut.before.logged.end_subset valid.1 (locks 0) (unique 0) jointInside
 have physical := List.Subset.trans locksInside jointFacts.2
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 have sourceG : source∈G := pays
 have shape := AboveOther11.head_shape i heroInside physical sourceG cut.headChecked metadata
 have quietG := TransportQuiet11.Quiet.project cut.before valid.1 (unique 0) jointInside G (by decide) (by decide)
 have fixedG := QuietGroupFixed11.whole_fixed quietG (by intro c h d;exact h)
 have tagG := no_push_unchanged G cut.beforeOutcomes fixedG
 have included := end_subset_selected cut.before.logged valid.1 G (endGroup Other before)
   (by decide) currentOther.1 owns currentOther.2
 have ownsBefore : G⊆endGroup Other (before++cut.beforeOutcomes) := by
  rw [endGroup_append]
  intro c h
  exact included (by rw [tagG];exact h)
 let headFirst := first.append cut.before.logged
 have allEffects : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes := by
  simp only [List.append_assoc]
  exact congrArg (List.append before) cut.outcomesEq.symm
 rcases shape with ⟨rfl,east⟩|⟨rfl,east⟩
 ·have facts := headFirst.end_subset (by decide) Other (by decide) (by decide)
  have row := CentralFirst11.exit_row (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant headFirst.trace)
    facts.1 facts.2 cut.headChecked cut.headEffect ⟨266,ownsBefore (by decide),metadata,Or.inl ⟨Or.inl rfl,east⟩⟩
  have gap := logged_event_gap_le headFirst cut.headChecked cut.headEffect cut.after Other (by decide) (by decide)
  have bound := Int.le_trans row gap
  change 2≤energy soko1_1.initial final Other ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes) at bound
  rw [allEffects,zero] at bound
  omega
 ·have target : pushTargets soko1_1.board 317 cut.direction=[318] := by rw [east];decide +kernel
  have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) headFirst.trace.holes_sublist.subset
  have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [east] using cut.headChecked
  have effect : Matches cut.middle cut.actor (.push 317 (.stay 318)) := by simpa only [headEq] using cut.headEffect
  have normalized := allEffects
  rw [headEq] at normalized
  have zeroHere : energy soko1_1.initial final Other ((before++cut.beforeOutcomes)++.push 317 (.stay 318)::cut.afterOutcomes)=0 := by rw [normalized];exact zero
  exact OtherTrap31811.impossible headFirst checked effect cut.after completed zeroHere ownsBefore
#print axioms find
#print axioms impossible
end Owner1007.AboveOtherZero11
