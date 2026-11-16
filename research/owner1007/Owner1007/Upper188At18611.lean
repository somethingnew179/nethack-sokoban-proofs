import Owner1007.Upper188TagPrice11
import Owner1007.UpperFirstCut11
import Owner1007.QuietFixed11
import Owner1007.HeroEnergyTrace11
import Owner1007.UpperBudget11
import Owner1007.HeroEnergySubset11
namespace Owner1007.Upper188At18611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def check (phase : Nat) : Bool :=
 (NetHack.SokobanLinearPhases.Map11.certificate.heroes phase).all fun hero=>
  decide (-22≤NetHack.Soko11Hero315.weight phase hero 186)
theorem checked : (List.range 17).all check=true:=by decide +kernel
theorem value_floor {state : State}
 (valid : HazardPhases.Good NetHack.SokobanLinearPhases.Map11.certificate state) : -22≤value state [186]:=by
 obtain ⟨phase,atIndex⟩:=valid.2
 have bound : phase<17:=by have bound:=atIndex.1;change phase≤16 at bound;omega
 have row:=of_decide_eq_true (List.all_eq_true.mp
  (List.all_eq_true.mp checked phase (List.mem_range.mpr bound)) state.player atIndex.2.2.1)
 have phaseEq:=HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 simpa only [value,NetHack.Sokoban.LowerBounds.weightSum,weightAt,phaseEq,Int.add_zero] using row

theorem two_pushes {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (tag : endGroup [188] outcomes=[186]) : 2≤ownPushes [188] outcomes:=by
 apply Classical.byContradiction
 intro contrary
 have limited : ownPushes [188] outcomes≤1:=by omega
 rcases first_cut_or_quiet (paid:=fun _ _=>True) logged [188] with found|quiet
 ·obtain ⟨cut⟩:=found
  have quietZero:=cut.before.fixed (by simp :188∈[188]) (by intro d;trivial)
  have beforeTag:=no_push_unchanged [188] cut.beforeOutcomes quietZero
  obtain ⟨source,owner,metadata,_⟩:=cut.headPaid
  have sourceEq : source=188:=by rw [beforeTag] at owner;simpa using owner
  subst source
  have headOwn : ownPush [188] cut.headOutcome=1:=by
   cases ef:cut.headOutcome with
   | walk target =>
    have e:=cut.headEffect
    rw [ef] at e
    simp only [Matches] at e
    simp only [e] at metadata
    contradiction
   | push source ending =>
    have other : source=188:=by
     cases ending with
     | stay target => have e:=cut.headEffect;rw [ef] at e;simpa only [e.2,Option.some.injEq] using metadata
     | fill target => have e:=cut.headEffect;rw [ef] at e;simpa only [e.2.2,Option.some.injEq] using metadata
    simp [ownPush,other]
  have limit:=limited
  rw [cut.outcomesEq,ownPushes_append,beforeTag] at limit
  simp only [ownPushes] at limit
  have tailZero : ownPushes (update [188] cut.headOutcome) cut.afterOutcomes=0:=by omega
  have tailTag:=no_push_unchanged (update [188] cut.headOutcome) cut.afterOutcomes tailZero
  have singleUpdate : update [188] cut.headOutcome=[186]:=by
   have totalTag:=tag
   rw [cut.outcomesEq,endGroup_append,beforeTag] at totalTag
   change endGroup (update [188] cut.headOutcome) cut.afterOutcomes=[186] at totalTag
   rwa [tailTag] at totalTag
  have effect : Matches cut.middle cut.actor (.push 188 (.stay 186)):=by
   have original:=cut.headEffect
   cases ef:cut.headOutcome with
   | walk target => simp only [ef,update] at singleUpdate;contradiction
   | push source ending =>
    have sourceEq : source=188:=by
     cases ending with
     | stay target => rw [ef] at original;simpa only [original.2,Option.some.injEq] using metadata
     | fill target => rw [ef] at original;simpa only [original.2.2,Option.some.injEq] using metadata
    subst source
    cases ending with
    | fill target => simp [ef,update,move,post] at singleUpdate
    | stay target =>
     have targetEq : target=186:=by simpa [ef,update,move,post] using singleUpdate
     subst target
     simpa only [ef] using original
  have targetMember : 186∈pushTargets soko1_1.board 188 cut.direction:=by
   rcases step_cases_full _ _ _ _ cut.headChecked with walked|pushed
   ·obtain ⟨target,_,_,_,_,shape⟩:=walked
    simp only [shape] at metadata
    contradiction
   ·obtain ⟨other,result,_,_,_,push,shape⟩:=pushed
    have otherEq : other=188:=by simpa only [shape,Option.some.injEq] using metadata
    subst other
    have landed : result.landing=186:=by
     have eq : cut.actor.landing=some 186:=by rw [effect.2]
     simpa only [shape,Option.some.injEq] using eq
    simpa only [landed] using (pushBoulder_spec _ _ _ _ _ push).2
  have all : allDirs.all (fun dir=>decide (186∉pushTargets soko1_1.board 188 dir))=true:=by decide +kernel
  have no186:=of_decide_eq_true (List.all_eq_true.mp all cut.direction (Geometry.all_directions cut.direction))
  exact no186 targetMember
 ·have zero:=quiet.fixed (by simp :188∈[188]) (by intro d;trivial)
  have same:=no_push_unchanged [188] outcomes zero
  rw [tag] at same
  contradiction

theorem at186_four {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (tag : endGroup [188] outcomes=[186]) :
 4≤energy soko1_1.initial state [188] outcomes:=by
 have positive:=two_pushes logged tag
 have current:=value_floor (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant logged.trace)
 have sameLength : (endGroup [188] outcomes).length=([188]:List Cell).length:=by rw [tag];rfl
 have credits:=full_survivor_credits_zero (HeroLedger.holeOnly NetHack.Soko11Hero315.holeWeight) [188] outcomes sameLength
 have charges:=HeroLedger.charges_eq_own NetHack.Soko11Hero315.holeWeight [188] outcomes
 have initial : value soko1_1.initial [188]= -24:=by decide +kernel
 unfold Hero315Frame11.energy HeroLedger.energy
 rw [charges,credits,tag,initial]
 simp only [Int.sub_zero,Int.ofNat_eq_natCast]
 omega
theorem upper_six {dirs state pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (tag : endGroup [188] outcomes=[186])
 (pairTwo : 2≤energy soko1_1.initial state TightSplit11.A outcomes) :
 6≤energy soko1_1.initial state UpperBudget11.U6 outcomes:=by
 have ownFour:=at186_four logged tag
 have split:=Hero315Frame11.energy_split logged TightSplit11.A UpperBudget11.C (by decide) (by decide)
 change energy soko1_1.initial state UpperBudget11.U6 outcomes=_ at split
 have nested:=energy_subset (Trace.nil soko1_1.initial) logged [188] UpperBudget11.C
  (by decide) (by decide) (by decide) (by decide) (by decide)
 omega
#print axioms at186_four
#print axioms upper_six
end Owner1007.Upper188At18611
