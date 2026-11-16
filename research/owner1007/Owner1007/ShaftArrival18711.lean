import Owner1007.Shaft18711Proof
import Owner1007.RestCutAdvance11
namespace Owner1007.ShaftArrival18711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem arrival
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Shaft18711.locks Shaft18711.region Shaft18711.paid)
 {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)=0)
 (subset : ([265,266] : List Cell)⊆endGroup UpperBudget11.Rest before)
 (active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16) (hero : state.player=292) :
 ∃ cut : FirstCut Shaft18711.paid state [265,266] dirs final pushes moves outcomes,
   cut.headOutcome=.push 213 (.stay 187) ∧cut.actor.state.player=213 ∧
   ([187,266] : List Cell)⊆endGroup UpperBudget11.Rest (RestCutAdvance11.afterPrefix first cut) ∧
   energy cut.actor.state final [187,266] cut.afterOutcomes=0 := by
 have big := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have inside := List.Subset.trans subset big.2
 have zero := ZeroRestTail11.subset_zero first logged zeroRest [265,266] (by decide) subset
 obtain ⟨cut⟩ := Shaft18711.first_cut closed first.trace logged completed active hero inside zero
 have good : OwnedCorral11.Good Shaft18711.locks Shaft18711.region state [265,266] := by
   refine ⟨⟨0,by decide⟩,?_,?_⟩
   · rw [hero];decide +kernel
   · change ([265,266] : List Cell)⊆[265,266]
     exact List.Subset.refl _
 obtain ⟨sourceEq,north,headEq,nextPerm⟩ := Shaft18711.useful closed first.trace [265,266]
   (by decide) inside (by decide) good zero cut
 have perm : (RestCutAdvance11.next cut).Perm [187,266] := nextPerm
 have selectedPair : ([187,266] : List Cell)⊆RestCutAdvance11.next cut := fun _ member=>perm.mem_iff.mpr member
 have selectedRest := List.Subset.trans selectedPair (RestCutAdvance11.subset_after first cut (by decide) subset)
 have zeroPair := RestCutAdvance11.zero_after first cut (by decide) subset zeroRest [187,266] (by decide) selectedPair
 have effect : Matches cut.middle cut.actor (.push 213 (.stay 187)) := by simpa only [headEq] using cut.headEffect
 have heroAfter : cut.actor.state.player=213 := by rw [effect.2]
 exact ⟨cut,headEq,heroAfter,selectedRest,zeroPair⟩
#print axioms arrival
end Owner1007.ShaftArrival18711