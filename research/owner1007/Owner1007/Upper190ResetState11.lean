import Owner1007.UpperResetGuards11
import Owner1007.StationaryGuardsSix11
namespace Owner1007.Upper190ResetState11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem shape_check : ∀ i : Fin 19, (190:Cell)∈UpperZero11.locks i →
 (189:Cell)∈UpperZero11.region i → (191:Cell)∉UpperZero11.locks i →
 UpperZero11.locks i=[137,139,190] := by decide +kernel

theorem before_after {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 191))) :
 (endGroup originalGroup cut.beforeOutcomes).Perm [137,139,190] ∧
 (update (endGroup originalGroup cut.beforeOutcomes) cut.headOutcome).Perm originalGroup := by
 have good := quiet_good UpperZero11.closed cut.before (by decide) (by decide) (by decide) (by decide)
   original_good (by simp)
 obtain ⟨i,heroInside,locksInside⟩ := good
 have before := cut.before.logged.end_subset (by decide) originalGroup (by decide) (by decide)
 have bounded := endGroup_length_le originalGroup cut.beforeOutcomes
 change (endGroup originalGroup cut.beforeOutcomes).length≤3 at bounded
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have sourceIs : source=190 := Option.some.inj (metadata.symm.trans sourceEq)
 have own190 : 190∈endGroup originalGroup cut.beforeOutcomes := sourceIs ▸ owner
 have sourceLock := UpperQuiet11.lock_complete i _ bounded locksInside 190 own190
 have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
 have hero := ActorPrices11.support_of_check 190 cut.middle.player .east 189 (by decide +kernel)
   (step_player_clear _ _ _ _ checked).1 (PairPost11.source_adjacent checked sourceEq)
 obtain ⟨result,_,push⟩ := effect_push_data checked effect
 obtain ⟨landing,adjacent,_,_,empty⟩ := (push_first_clear soko1_1.board cut.middle 190 .east result push).2
 have landingEq : landing=191 := Option.some.inj (adjacent.symm.trans (by decide +kernel))
 have clear191 : 191∉cut.middle.boulders := landingEq ▸ empty
 have row := shape_check i sourceLock (by simpa only [hero] using heroInside)
   (fun found=>clear191 (before.2 (locksInside found)))
 have perm : (endGroup originalGroup cut.beforeOutcomes).Perm (UpperZero11.locks i) := by
   apply (List.perm_ext_iff_of_nodup before.1 (UpperZero11.unique i)).mpr
   intro cell
   exact ⟨fun found=>UpperQuiet11.lock_complete i _ bounded locksInside cell found,fun found=>locksInside found⟩
 rw [row] at perm
 have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome (.push 190 (.stay 191)) cut.headEffect effect
 have after := update_perm perm cut.headOutcome
 rw [headEq] at after
 have concrete : (update ([137,139,190] : List Cell) (.push 190 (.stay 191))).Perm originalGroup := by decide +kernel
 refine ⟨perm,?_⟩
 rw [headEq]
 exact after.trans concrete
#print axioms before_after

theorem stationary_before {dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 191))) :
 ownPushes [137] cut.beforeOutcomes=0 ∧ ownPushes [139] cut.beforeOutcomes=0 := by
 have shape := (before_after cut sourceEq directionEq effect).1
 constructor
 · exact cut.before.stationary UpperZero11.closed (by decide) (by decide) (by decide) (by decide)
     original_good (by simp) 137 (by simp) (shape.mem_iff.mpr (by simp))
 · exact cut.before.stationary UpperZero11.closed (by decide) (by decide) (by decide) (by decide)
     original_good (by simp) 139 (by simp) (shape.mem_iff.mpr (by simp))
#print axioms stationary_before

theorem guarded141_before {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 191)))
 (cheap : energy soko1_1.initial final U6 outcomes<6) :
 endGroup [141] cut.beforeOutcomes=[141] ∨ endGroup [141] cut.beforeOutcomes=[140] := by
 have still139 := (stationary_before cut sourceEq directionEq effect).2
 have prefixCheap := UpperResetGuards11.prefix_two logged completed cut 1 sourceEq directionEq effect cheap 141 (by decide)
 exact StationaryGuardsSix11.guard141 cut.before.logged still139 (by omega)
#print axioms guarded141_before
end Owner1007.Upper190ResetState11
