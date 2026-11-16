import Owner1007.Budget32811
import Owner1007.PairFirstCut11
import Owner1007.LoggedEventGap11
namespace Owner1007.UpperNineSurvivor11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pair_cut {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : energy soko1_1.initial final PairFirstCut11.originalGroup outcomes≤9) :
 Nonempty (FirstCut PairPath11.paid soko1_1.initial PairFirstCut11.originalGroup dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet logged PairFirstCut11.originalGroup with found|quiet
 ·exact found
 ·have persists:=PairFirstCut11.quiet_good PairPath11.closed PairPath11.unique PairPath11.size quiet
    (by decide) (by decide) (by decide) (by decide) PairFirstCut11.initial_good (by simp)
  obtain ⟨i,_,selected⟩:=persists
  have card:=List.Nodup.length_le_of_subset (PairPath11.unique i) selected
  rw [PairPath11.size i] at card
  have bound:=endGroup_length_le PairFirstCut11.originalGroup outcomes
  have same : (endGroup PairFirstCut11.originalGroup outcomes).length=PairFirstCut11.originalGroup.length := by
   change (endGroup PairFirstCut11.originalGroup outcomes).length≤2 at bound
   change (endGroup PairFirstCut11.originalGroup outcomes).length=2
   omega
  have survivor:=HeroLedger.full_survivor_energy value NetHack.Soko11Hero315.holeWeight
   soko1_1.initial final PairFirstCut11.originalGroup outcomes same (goal_value_zero completed _)
  change energy soko1_1.initial final PairFirstCut11.originalGroup outcomes=
   Int.ofNat (ownPushes PairFirstCut11.originalGroup outcomes)-value soko1_1.initial PairFirstCut11.originalGroup at survivor
  have debt : value soko1_1.initial PairFirstCut11.originalGroup= -34 := by decide +kernel
  have nn : (0:Int)≤Int.ofNat (ownPushes PairFirstCut11.originalGroup outcomes) := Int.natCast_nonneg _
  omega

theorem gate139_gone {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cap : energy soko1_1.initial final UpperBudget11.U6 outcomes≤9) :
 endGroup [139] outcomes=[] := by
 by_cases gone : endGroup [139] outcomes=[]
 ·exact gone
 have survivor:=survivor_energy logged completed 139 gone
 have initial : value soko1_1.initial [139]= -9 := by decide +kernel
 have bound139:=energy_subset (Trace.nil soko1_1.initial) logged [139] UpperBudget11.U6
  (by decide) (by decide) (by decide) (by decide) (by decide)
 have zero : ownPushes [139] outcomes=0 := by rw [initial] at survivor;simp only[Int.ofNat_eq_natCast] at survivor;omega
 have nine : energy soko1_1.initial final [139] outcomes=9 := by rw[initial,zero] at survivor;simpa using survivor
 have pairBound:=energy_subset (Trace.nil soko1_1.initial) logged PairFirstCut11.originalGroup UpperBudget11.U6
  (by decide) (by decide) (by decide) (by decide) (by decide)
 obtain ⟨cut⟩:=pair_cut logged completed (by omega)
 have beforeZero : ownPushes [139] cut.beforeOutcomes=0 := by
  rw [cut.outcomesEq,ownPushes_append] at zero
  omega
 have tag139:=no_push_unchanged [139] cut.beforeOutcomes beforeZero
 obtain ⟨source,owner,metadata,paid⟩:=cut.headPaid
 have not139 : source≠139 := by
  intro equal
  subst source
  have effect:=cut.headEffect
  cases eq:cut.headOutcome with
  |walk target=>
   rw[eq] at effect
   simp only[Matches] at effect
   simp only[effect] at metadata
   contradiction
  |push other ending=>
   have same : other=139 := by
    cases ending with
    |stay dest=>rw[eq] at effect;simpa only[effect.2,Option.some.injEq] using metadata
    |fill dest=>rw[eq] at effect;simpa only[effect.2.2,Option.some.injEq] using metadata
   have own : ownPush [139] cut.headOutcome=1 := by simp[eq,same,ownPush]
   have count:=zero
   rw[cut.outcomesEq,ownPushes_append,tag139] at count
   simp only[ownPushes] at count
   omega
 have split:=HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [139] [191] (by decide) (by decide)
 rw[tag139] at split
 have source191 : source∈endGroup [191] cut.beforeOutcomes := by
  have member:=split.mem_iff.mp owner
  rcases List.mem_append.mp member with h|h
  ·exact False.elim (not139 (List.mem_singleton.mp h))
  ·exact h
 have selected:=cut.before.logged.end_subset (by decide) [191] (by decide) (by decide)
 have row:=PairStrict11.exit_row scalar rfl
  (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace)
  cut.headChecked cut.headEffect selected.1 selected.2 ⟨source,source191,metadata,paid⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup [191] cut.beforeOutcomes) cut.headOutcome+
  value cut.actor.state (update (endGroup [191] cut.beforeOutcomes) cut.headOutcome)-
  value cut.middle (endGroup [191] cut.beforeOutcomes) at row
 have price:=logged_event_gap_le cut.before.logged cut.headChecked cut.headEffect cut.after [191] (by decide) (by decide)
 have two : 2≤energy soko1_1.initial final [191] outcomes := by
  rw[cut.outcomesEq]
  omega
 have pairSplit:=Hero315Frame11.energy_split logged [139] [191] (by decide) (by decide)
 change energy soko1_1.initial final PairFirstCut11.originalGroup outcomes=_ at pairSplit
 omega
#print axioms pair_cut
#print axioms gate139_gone
end Owner1007.UpperNineSurvivor11
