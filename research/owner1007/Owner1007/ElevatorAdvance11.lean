import Owner1007.LowerElevator11Proof
import Owner1007.Shaft18711Data
import Owner1007.RestCutAdvance11
namespace Owner1007.ElevatorAdvance11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
def G : List Cell := [266,292,317]
theorem start
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LowerElevator11.locks LowerElevator11.region LowerElevator11.paid)
 {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)=0)
 (subset : G⊆endGroup UpperBudget11.Rest before)
 (good : OwnedCorral11.Good LowerElevator11.locks LowerElevator11.region state G)
 (cut : FirstCut LowerElevator11.paid state G dirs final pushes moves outcomes) :
 cut.headOutcome=.push 292 (.stay 266) ∧cut.actor.state.player=292 ∧
 ([265,266] : List Cell)⊆endGroup UpperBudget11.Rest (RestCutAdvance11.afterPrefix first cut) ∧
 energy cut.actor.state final [265,266] cut.afterOutcomes=0 ∧
 HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes cut.actor.state<16 ∧
 OwnedCorral11.Good Shaft18711.locks Shaft18711.region cut.actor.state [265,266] ∧
 ownPushes [317] cut.beforeOutcomes=0 := by
 have big := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have inside := List.Subset.trans subset big.2
 have zero := ZeroRestTail11.subset_zero first logged zeroRest G (by decide) subset
 obtain ⟨sourceEq,north,headEq,nextPerm,fixed317⟩ := LowerElevator11.useful closed first.trace G
   (by decide) inside (by decide) good zero cut
 have perm : (RestCutAdvance11.next cut).Perm [265,266,317] := nextPerm
 have selectedPair : ([265,266] : List Cell)⊆RestCutAdvance11.next cut := by
   intro c member
   exact perm.mem_iff.mpr ((show ([265,266] : List Cell)⊆[265,266,317] from by decide) member)
 have selectedRest := List.Subset.trans selectedPair (RestCutAdvance11.subset_after first cut (by decide) subset)
 have zeroPair := RestCutAdvance11.zero_after first cut (by decide) subset zeroRest [265,266] (by decide) selectedPair
 have effect : Matches cut.middle cut.actor (.push 292 (.stay 266)) := by simpa only [headEq] using cut.headEffect
 have hero : cut.actor.state.player=292 := by rw [effect.2]
 have active := ZeroRestTail11.active_after_stay (first.trace.append cut.before.logged.trace) cut.headChecked effect
 have goodShaft : OwnedCorral11.Good Shaft18711.locks Shaft18711.region cut.actor.state [265,266] := by
   refine ⟨⟨0,by decide⟩,?_,?_⟩
   · rw [hero];decide +kernel
   · change ([265,266] : List Cell)⊆[265,266]
     exact List.Subset.refl _
 exact ⟨headEq,hero,selectedRest,zeroPair,active,goodShaft,fixed317⟩
#print axioms start
end Owner1007.ElevatorAdvance11