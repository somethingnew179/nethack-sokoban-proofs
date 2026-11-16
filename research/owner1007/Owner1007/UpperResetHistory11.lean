import Owner1007.UpperToPair11
import Owner1007.PairDAG11
import Owner1007.UpperEventEnergy11
namespace Owner1007.UpperResetHistory11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11

theorem head_pair_owned {dirs final pushes moves outcomes source}
 (cut : UpperFirstCut11.FirstCut UpperZero11.paid soko1_1.initial UpperFirstCut11.originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some source) (exit : CutActor11.Exit source cut.direction)
 (cheap137 : energy soko1_1.initial final [137] outcomes<2) :
 source∈endGroup PairFirstCut11.originalGroup cut.beforeOutcomes := by
 obtain ⟨other,owner,metadata,_⟩ := cut.headPaid
 have same : other=source := Option.some.inj (metadata.symm.trans sourceEq)
 have selectedSource : source∈endGroup UpperFirstCut11.originalGroup cut.beforeOutcomes := same ▸ owner
 have split := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [137] PairFirstCut11.originalGroup (by decide) (by decide)
 have member : source∈endGroup [137] cut.beforeOutcomes ++ endGroup PairFirstCut11.originalGroup cut.beforeOutcomes :=
   split.mem_iff.mp selectedSource
 rcases List.mem_append.mp member with in137|inPair
 · have before := cut.before.logged.end_subset (by decide) [137] (by decide) (by decide)
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have row := CutStrict11.exit_row scalar rfl valid cut.headChecked cut.headEffect before.1 before.2
     ⟨source,in137,sourceEq,exit⟩
   change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [137] cut.beforeOutcomes) cut.headOutcome +
     value cut.actor.state (update (endGroup [137] cut.beforeOutcomes) cut.headOutcome)-
     value cut.middle (endGroup [137] cut.beforeOutcomes) at row
   have bound := UpperEventEnergy11.event_gap_le cut [137] (by decide) (by decide)
   omega
 · exact inPair

theorem before138east {dirs final pushes moves outcomes}
 (cut : UpperFirstCut11.FirstCut UpperZero11.paid soko1_1.initial UpperFirstCut11.originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 138) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push 138 (.stay 139)))
 (cheap137 : energy soko1_1.initial final [137] outcomes<2) :
 ownPushes [139] cut.beforeOutcomes≤1 ∧ endGroup [139] cut.beforeOutcomes=[138] := by
 have owner := head_pair_owned cut sourceEq (by simp [CutActor11.Exit,directionEq]) cheap137
 have pays : OwnedCorral11.PaidStep PairPath11.paid
     (endGroup PairFirstCut11.originalGroup cut.beforeOutcomes) cut.direction cut.actor :=
   ⟨138,owner,sourceEq,by simp [PairPath11.paid,directionEq]⟩
 let pairCut := UpperToPair11.as_pair cut pays
 have perm := PairPost11.before_after (support:=137) (source:=138) (landing:=139) (dir:=.east)
   (old:=[138,191]) (next:=[139,191]) pairCut (by simp [PairPost11.edges]) sourceEq directionEq effect
 exact PairDAG11.before138 pairCut.before perm.1
#print axioms before138east

theorem before190east {dirs final pushes moves outcomes}
 (cut : UpperFirstCut11.FirstCut UpperZero11.paid soko1_1.initial UpperFirstCut11.originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 191)))
 (cheap137 : energy soko1_1.initial final [137] outcomes<2) :
 ownPushes [191] cut.beforeOutcomes≤1 ∧ endGroup [191] cut.beforeOutcomes=[190] := by
 have owner := head_pair_owned cut sourceEq (by simp [CutActor11.Exit,directionEq]) cheap137
 have pays : OwnedCorral11.PaidStep PairPath11.paid
     (endGroup PairFirstCut11.originalGroup cut.beforeOutcomes) cut.direction cut.actor :=
   ⟨190,owner,sourceEq,by simp [PairPath11.paid,directionEq]⟩
 let pairCut := UpperToPair11.as_pair cut pays
 have perm := PairPost11.before_after (support:=189) (source:=190) (landing:=191) (dir:=.east)
   (old:=[139,190]) (next:=[139,191]) pairCut (by simp [PairPost11.edges]) sourceEq directionEq effect
 exact PairDAG11.before190 pairCut.before perm.1
#print axioms before190east
end Owner1007.UpperResetHistory11
