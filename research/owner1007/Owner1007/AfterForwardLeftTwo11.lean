import Owner1007.AfterForwardSeven11
import Owner1007.ForwardSnapshots11
import Owner1007.ForwardLeftWest11
import Owner1007.ForwardResetEight11
import Owner1007.UpperExtraWestEight11
import Owner1007.ForwardInwardImpossible11
import Owner1007.Upper188TagPrice11
import Owner1007.First137RestAnywhere11
import Owner1007.Gate139EastImpossible11
namespace Owner1007.AfterForwardLeftTwo11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem impossible {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : beforePushes+pushes≤327)
 (capUpper : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6)
 (capLeft : energy soko1_1.initial final [186] (before++outcomes)≤2)
 (capRest : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2)
 (prefixUpper : 4≤energy soko1_1.initial state UpperBudget11.U6 before)
 (prefixLeft : 2≤energy soko1_1.initial state [186] before)
 (prefixPair : 2≤energy soko1_1.initial state TightSplit11.A before)
 (tag186 : endGroup [186] before=[185]) (tag188 : endGroup [188] before=[187]) (tag191 : endGroup [191] before=[189])
 (fixed137 : ownPushes [137] before=0) (fixed139 : ownPushes [139] before=0) (player : state.player=190) : False := by
 have sameStart:=ForwardSnapshots11.five_perm first fixed137 fixed139 tag186 tag188 tag191
 have sameInitial : (endGroup ForwardSnapshots11.G before).Perm (AfterForwardSeven11.locks 0) := sameStart
 have facts:=first.end_subset (by decide) ForwardSnapshots11.G (by decide) (by decide)
 have startHero : state.player∈AfterForwardSeven11.region 0 := by rw [player];decide +kernel
 obtain ⟨cut,j,beforeSame,leftTag,upperTag,rightTag,beforeHero⟩:=AfterForwardSeven11.first_packet first logged completed cheap 0 sameInitial facts.2 startHero
 let current:=first.append cut.before.logged
 have sequence : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes := by
  calc
   _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes):=by simp only [List.append_assoc]
   _=before++outcomes:=congrArg (List.append before) cut.outcomesEq.symm
 have currentUpper : energy soko1_1.initial final UpperBudget11.U6 ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)≤6 := by rw [sequence];exact capUpper
 have currentLeft : energy soko1_1.initial final [186] ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)≤2 := by rw [sequence];exact capLeft
 have currentRest : energy soko1_1.initial final UpperBudget11.Rest ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)<2 := by rw [sequence];exact capRest
 have monoUpper:=prefix_energy_le first cut.before.logged UpperBudget11.U6 (by decide) (by decide)
 have monoLeft:=prefix_energy_le first cut.before.logged [186] (by decide) (by decide)
 have monoPair:=prefix_energy_le first cut.before.logged TightSplit11.A (by decide) (by decide)
 have currentPrefixUpper : 4≤energy soko1_1.initial cut.middle UpperBudget11.U6 (before++cut.beforeOutcomes) := by omega
 have currentPrefixLeft : 2≤energy soko1_1.initial cut.middle [186] (before++cut.beforeOutcomes) := by omega
 have currentPrefixPair : 2≤energy soko1_1.initial cut.middle TightSplit11.A (before++cut.beforeOutcomes) := by omega
 have initialOther:=Upper188TagPrice11.at187_two first tag188
 have otherBound:=prefix_energy_le first logged [188] (by decide) (by decide)
 have otherTwo : 2≤energy soko1_1.initial final [188] ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes) := by rw [sequence];omega
 have currentTag186 : endGroup [186] (before++cut.beforeOutcomes)=[AfterForwardSeven11.left j] := by rw [endGroup_append,tag186];exact leftTag
 have currentTag188 : endGroup [188] (before++cut.beforeOutcomes)=[AfterForwardSeven11.upper j] := by rw [endGroup_append,tag188];exact upperTag
 have currentTag191 : endGroup [191] (before++cut.beforeOutcomes)=[AfterForwardSeven11.right j] := by rw [endGroup_append,tag191];exact rightTag
 have owns137 : 137∈endGroup ForwardSnapshots11.G before := sameStart.mem_iff.mpr (by decide)
 have owns139 : 139∈endGroup ForwardSnapshots11.G before := sameStart.mem_iff.mpr (by decide)
 have local137:=cut.before.fixed owns137 (by intro d;exact Or.inl rfl)
 have local139:=cut.before.fixed owns139 (by intro d;exact Or.inr (Or.inl rfl))
 have currentFixed137 : ownPushes [137] (before++cut.beforeOutcomes)=0 := by
  rw [ownPushes_append,no_push_unchanged _ _ fixed137,fixed137,local137]
 have currentFixed139 : ownPushes [139] (before++cut.beforeOutcomes)=0 := by
  rw [ownPushes_append,no_push_unchanged _ _ fixed139,fixed139,local139]
 have currentSame : (endGroup ForwardSnapshots11.G (before++cut.beforeOutcomes)).Perm (AfterForwardSeven11.locks j) := by
  rw [endGroup_append];exact beforeSame
 have beforeActual:=(NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
 have currentFacts:=cut.before.logged.end_subset beforeActual (endGroup ForwardSnapshots11.G before) facts.1 facts.2
 have currentCheap : (beforePushes+cut.beforePushes)+cut.actor.pushCost+cut.afterPushes≤327 := by have eq:=cut.pushesEq;omega
 obtain ⟨source,owner,metadata,shape⟩:=AfterForwardSeven11.head_shape j beforeSame currentFacts.2 beforeHero cut.headChecked cut.headPaid
 rcases shape with ⟨gates,phaseZero⟩|⟨isLeft,west⟩|⟨isUpper,upperSources,west⟩|⟨isRight,is190,directions⟩
 ·have jZero : j=0:=Fin.ext phaseZero
  have literalSame : (endGroup ForwardSnapshots11.G (before++cut.beforeOutcomes)).Perm [137,139,185,187,189] := by
   have lockZero : AfterForwardSeven11.locks 0=[137,139,185,187,189] := by decide +kernel
   simpa only [jZero,lockZero] using currentSame
  rcases gates with rfl|rfl
  ·rcases RightEarlyWords11.gate_direction (show 137∈([137,139]:List Cell) by decide) cut.headChecked metadata with east|west
   ·have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [east] using cut.headChecked
    have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 137 .east=[138] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 137 (.stay 138)) := by simpa only [outEq] using cut.headEffect
    rw [outEq] at currentUpper currentLeft currentRest
    exact ForwardInwardImpossible11.impossible current 0 checked effect cut.after completed currentUpper currentLeft currentRest
     currentPrefixUpper currentPrefixLeft literalSame currentFixed139
   ·have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
    have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 137 .west=[136] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)) := by simpa only [outEq] using cut.headEffect
    have reserve:=First137RestAnywhere11.rest_two current checked effect cut.after completed currentFixed137
    rw [outEq] at currentRest
    omega
  ·rcases RightEarlyWords11.gate_direction (show 139∈([137,139]:List Cell) by decide) cut.headChecked metadata with east|west
   ·have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [east] using cut.headChecked
    have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)) := by simpa only [outEq] using cut.headEffect
    rw [outEq] at currentUpper
    exact Gate139EastImpossible11.impossible current checked effect cut.after completed (by omega) currentFixed139
   ·have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
    have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 139 .west=[138] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 139 (.stay 138)) := by simpa only [outEq] using cut.headEffect
    rw [outEq] at currentUpper currentLeft currentRest
    exact ForwardInwardImpossible11.impossible current 1 checked effect cut.after completed currentUpper currentLeft currentRest
     currentPrefixUpper currentPrefixLeft literalSame currentFixed137
 ·have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
  have sourceEq : cut.actor.pushSource=some (AfterForwardSeven11.left j) := metadata.trans (congrArg some isLeft)
  have sources : AfterForwardSeven11.left j∈([185,186,187]:List Cell) := by
   have row : ∀i : Fin 7,AfterForwardSeven11.left i∈([185,186,187]:List Cell) := by decide +kernel
   exact row j
  have four:=ForwardLeftWest11.four current checked cut.headEffect cut.after currentTag186 sourceEq sources currentPrefixLeft
  omega
 ·rcases upperSources with rfl|rfl
  ·have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
   have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 187 .west=[186] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 187 (.stay 186)) := by simpa only [outEq] using cut.headEffect
   have left185 : AfterForwardSeven11.left j=185 := by
    have row : ∀i : Fin 7,AfterForwardSeven11.upper i=187→AfterForwardSeven11.left i=185 := by decide +kernel
    exact row j isUpper.symm
   have present185 : 185∈cut.middle.boulders := currentFacts.2 (beforeSame.mem_iff.mpr (by simp [AfterForwardSeven11.locks,left185]))
   have physical : [185,186]⊆cut.actor.state.boulders := by
    rw [effect.2]
    intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :185≠187)).mpr present185)
    ·exact List.mem_cons_self
   let headLogged : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
    .cons cut.headChecked cut.headEffect (.nil _)
   exact LeftTwoLaneForward11.frozen185186 (current.append headLogged) cut.after completed currentCheap physical
  ·have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
   have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 188 .west=[187] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 188 (.stay 187)) := by simpa only [outEq] using cut.headEffect
   have right190 : AfterForwardSeven11.right j=190 := by
    have row : ∀i : Fin 7,AfterForwardSeven11.upper i=188→AfterForwardSeven11.right i=190 := by decide +kernel
    exact row j isUpper.symm
   have zPerm:=ForwardSnapshots11.three_perm current currentFixed137 currentFixed139 currentTag191
   rw [right190] at zPerm
   have tag : endGroup [188] (before++cut.beforeOutcomes)=[188] := by simpa only [isUpper.symm] using currentTag188
   have eight:=UpperExtraWestEight11.upper_eight current checked effect cut.after completed zPerm tag currentPrefixUpper
   rw [outEq] at currentUpper
   omega
 ·rcases is190 with rfl
  have right190 : AfterForwardSeven11.right j=190 := isRight.symm
  rcases directions with north|east
  ·have checked : step soko1_1.board cut.middle .north=some cut.actor := by simpa only [north] using cut.headChecked
   have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 190 .north=[164] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 190 (.stay 164)) := by simpa only [outEq] using cut.headEffect
   rw [outEq] at currentUpper currentRest
   have moved:=UpperShaftGate11.gate_moved_before_north current checked effect cut.after completed (by omega) currentRest
   omega
  ·have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [east] using cut.headChecked
   have outEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 190 .east=[191] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 190 (.stay 191)) := by simpa only [outEq] using cut.headEffect
   have pairPerm:=ForwardSnapshots11.pair_perm current currentFixed139 currentTag191
   rw [right190] at pairPerm
   rw [outEq] at otherTwo currentUpper
   have eight:=ForwardResetEight11.upper_eight current checked effect cut.after completed pairPerm currentPrefixPair otherTwo
   omega
#print axioms impossible
end Owner1007.AfterForwardLeftTwo11
