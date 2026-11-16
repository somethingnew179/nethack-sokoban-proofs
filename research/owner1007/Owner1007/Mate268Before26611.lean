import Owner1007.Gate265Markers11
import Owner1007.StationaryGuards11
import Owner1007.Upper216Eight11
namespace Owner1007.Mate268Before26611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guards : (List.range 16).all (StationaryGuards11.guardCheck 266 [268,267])=true := by decide +kernel

theorem no_first_east {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .east=some t) (effect : Matches state t (.push 266 (.stay 267)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (stationary : ownPushes [266] before=0)
 (cheap268 : energy soko1_1.initial final [268] (before++.push 266 (.stay 267)::after)<2)
 (gone266 : endGroup [266] (before++.push 266 (.stay 267)::after)=[]) : False := by
 have bound := prefix_energy_le first (Logged.cons head effect last) [268] (by decide) (by decide)
 have prefixCheap : energy soko1_1.initial state [268] before<2 := by omega
 obtain ⟨next,member,tag⟩ := StationaryGuards11.guard_logged guards first
   NetHack.SokobanLinearPhases.Map11.initial_good (by decide) (by decide) (by simp) stationary prefixCheap
 have selected := (first.end_subset (by decide) [268] (by decide) (by decide)).2
 have targetClear : 267∉state.boulders := by
  obtain ⟨result,_,push⟩ := effect_push_data head effect
  obtain ⟨dest,adjacent,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
  have same : dest=267 := Option.some.inj (adjacent.symm.trans (show advance soko1_1.board 266 .east=some 267 by decide +kernel))
  exact same ▸ clear
 have tag268 : endGroup [268] before=[268] := by
  rcases List.mem_cons.mp member with rfl|later
  ·exact tag
  ·have same : next=267 := List.mem_singleton.mp later
   subst next
   exact False.elim (targetClear (selected (by rw [tag];simp)))
 have physical : ([267,268] : List Cell)⊆t.state.boulders := by
  rw [effect.2]
  intro c h
  rcases List.mem_cons.mp h with rfl|later
  ·exact List.mem_cons_self
  ·have same : c=268 := List.mem_singleton.mp later
   subst c
   exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :268≠266)).mpr (selected (by rw [tag268];simp)))
 have tag266 := no_push_unchanged [266] before stationary
 rw [endGroup_append,tag266] at gone266
 change endGroup [267] after=[] at gone266
 have actual := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
 exact Upper216Eight11.frozen_absurd (cell:=267) last (step_boulders_nodup _ _ _ _ actual head) (by decide)
  (by simpa using physical (by decide :267∈([267,268] : List Cell)))
  (Owner1007.locked_of_check _ [267,268] (by decide +kernel)) physical (by decide) (by decide) gone266
#print axioms guards
#print axioms no_first_east
end Owner1007.Mate268Before26611
namespace Owner1007.Mate268Before26611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stationary_before_boundary {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (cheap268 : energy soko1_1.initial final [268] outcomes<2)
 (gone266 : endGroup [266] outcomes=[]) : ownPushes [266] boundary.beforeOutcomes=0 := by
 rcases first_cut_or_quiet (paid:=fun _ _=>True) boundary.before.logged [266] with found|quiet
 ·obtain ⟨first⟩ := found
  have fixed := first.before.fixed (by simp :266∈([266] : List Cell)) (by intro d;trivial)
  have tag := no_push_unchanged [266] first.beforeOutcomes fixed
  obtain ⟨source,owner,metadata,_⟩ := first.headPaid
  rw [tag] at owner
  have same : source=266 := List.mem_singleton.mp owner
  subst source
  have actual266 : 266∈first.middle.boulders := (first.before.logged.end_subset (by decide) [266] (by decide) (by decide)).2 (by rw [tag];simp)
  let last := first.after.append (Logged.cons boundary.headChecked boundary.headEffect boundary.after)
  have allEffects : first.beforeOutcomes++first.headOutcome::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes)=outcomes := by
   calc
    _=(first.beforeOutcomes++first.headOutcome::first.afterOutcomes)++boundary.headOutcome::boundary.afterOutcomes := by simp only [List.append_assoc,List.cons_append]
    _=boundary.beforeOutcomes++boundary.headOutcome::boundary.afterOutcomes := congrArg (fun before=>before++boundary.headOutcome::boundary.afterOutcomes) first.outcomesEq.symm
    _=outcomes := boundary.outcomesEq.symm
  rcases Gate265Markers11.head_ew (by decide) actual266 first.headChecked metadata with east|west
  ·have target : pushTargets soko1_1.board 266 first.direction=[267] := by rw [east];decide +kernel
   have headEq := UpperHeadCases11.ordinary_effect first.headChecked first.headEffect metadata target (by decide +kernel) first.before.logged.trace.holes_sublist.subset
   have checked : step soko1_1.board first.middle .east=some first.actor := by simpa only [east] using first.headChecked
   have effect : Matches first.middle first.actor (.push 266 (.stay 267)) := by simpa only [headEq] using first.headEffect
   have normalized := allEffects
   rw [headEq] at normalized
   have cheap : energy soko1_1.initial final [268] (first.beforeOutcomes++.push 266 (.stay 267)::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes))<2 := by rw [normalized];exact cheap268
   have gone : endGroup [266] (first.beforeOutcomes++.push 266 (.stay 267)::(first.afterOutcomes++boundary.headOutcome::boundary.afterOutcomes))=[] := by rw [normalized];exact gone266
   exact False.elim (no_first_east first.before.logged checked effect last fixed cheap gone)
  ·have zero := FirstRest18711.quiet_count_zero boundary.before
   have actualOwner : 266∈endGroup soko1_1.initial.boulders first.beforeOutcomes := by
    rw [HeroLedger.Logged.end_all first.before.logged]
    exact actual266
   have pays : OwnedCorral11.PaidStep Gate265Transport11.paid
       (endGroup soko1_1.initial.boulders first.beforeOutcomes) first.direction first.actor :=
     ⟨266,actualOwner,metadata,Or.inr (Or.inr (Or.inl ⟨rfl,west⟩))⟩
   have positive := PaidCount11.event_le (paid:=Gate265Transport11.paid) (lastDirs:=first.afterDirs) (last:=first.afterOutcomes)
     first.before.logged first.headEffect soko1_1.initial.boulders pays
   rw [←first.dirsEq,←first.outcomesEq,zero] at positive
   omega
 ·exact quiet.fixed (by simp :266∈([266] : List Cell)) (by intro d;trivial)
#print axioms stationary_before_boundary
end Owner1007.Mate268Before26611
