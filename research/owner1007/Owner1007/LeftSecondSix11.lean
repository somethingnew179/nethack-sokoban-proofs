import Owner1007.LeftFirstTwoEight11
import Owner1007.LeftSameActor11
namespace Owner1007.LeftSecondSix11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.LeftSameActor11
theorem same_second {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (cut : FirstCut LeftPair11.paid state (endGroup [186,212] before) dirs final pushes moves outcomes)
 (completed : Goal final)
 (i : Fin 2) (same : (endGroup [186,212] before).Perm (LeftPair11.locks i))
 (hero : state.player∈LeftPair11.region i)
 (cashFirst : 1≤PaidCount11.count LeftPair11.paid [186,212] beforeDirs before)
 (cheap : energy soko1_1.initial final [186,212] (before++outcomes)≤6) :
 cut.actor.pushSource=some (landing i) := by
 have facts := first.end_subset (by decide) [186,212] (by decide) (by decide)
 have bounded := endGroup_length_le [186,212] before
 change (endGroup [186,212] before).length≤2 at bounded
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have quiet := LeftFirstTwo11.quiet_same cut.before valid.1 facts.1 facts.2 bounded i same hero first.trace.holes_sublist.subset
 obtain ⟨source,owner,metadata,pays⟩:=cut.headPaid
 have member : source∈LeftPair11.locks i := quiet.2.mem_iff.mp owner
 rcases source_cases i source member with sameActor|otherActor
 · exact metadata.trans (congrArg some sameActor)
 · have other : cut.actor.pushSource=some (LeftFirstTwo11.otherSource i) := metadata.trans (congrArg some otherActor)
   have eight := LeftFirstTwoEight11.eight_of_other_second first cut completed i same hero other cashFirst
   omega
#print axioms same_second
end Owner1007.LeftSecondSix11
