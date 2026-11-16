import Owner1007.LeadingSideRestTwo11
import Owner1007.Front26511Proof
import Owner1007.TransportEvents11
namespace Owner1007.ModeCFrontQuiet11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 (Rest)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem quiet_after {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last)
 (below : ∃source,source∈endGroup Rest boundary.beforeOutcomes ∧
   boundary.actor.pushSource=some source ∧
   ((source=264∧boundary.direction=.east)∨(source=266∧boundary.direction=.west)∨(source=291∧boundary.direction=.north)))
 (restCap : energy soko1_1.initial final Rest (outcomes++last)≤2)
 (noNorth : PaidCount11.count FirstRest18711.paid Rest dirs outcomes=0) :
 UpperQuiet11.Quiet Front26511.paid boundary.actor.state [265] boundary.afterDirs state
   boundary.afterPushes boundary.afterMoves boundary.afterOutcomes := by
 obtain ⟨source,sourceOwner,metadata,shape⟩ := below
 have target : pushTargets soko1_1.board source boundary.direction=[265] := by
  rcases shape with ⟨rfl,east⟩|⟨rfl,west⟩|⟨rfl,north⟩
  ·rw [east];decide +kernel
  ·rw [west];decide +kernel
  ·rw [north];decide +kernel
 have headEq := UpperHeadCases11.ordinary_effect boundary.headChecked boundary.headEffect metadata target
   (by decide +kernel) boundary.before.logged.trace.holes_sublist.subset
 have effect : Matches boundary.middle boundary.actor (.push source (.stay 265)) := by simpa only [headEq] using boundary.headEffect
 let one : Logged soko1_1.board boundary.middle [boundary.direction] boundary.actor.state boundary.actor.pushCost 1 [boundary.headOutcome] :=
   .cons boundary.headChecked boundary.headEffect (.nil _)
 let firstAfter := boundary.before.logged.append one
 let effectsB := boundary.beforeOutcomes++[boundary.headOutcome]
 have afterValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant firstAfter.trace
 have afterRest := firstAfter.end_subset (by decide) Rest (by decide) (by decide)
 have frontOwner : 265∈endGroup Rest effectsB := by
  rw [endGroup_append]
  change 265∈update (endGroup Rest boundary.beforeOutcomes) boundary.headOutcome
  rw [headEq]
  simp only [update,move,if_pos sourceOwner,post]
  exact List.mem_cons_self
 have frontActual : 265∈boundary.actor.state.boulders := by rw [effect.2];simp
 have heroLower : boundary.actor.state.player∈Gate265Transport11.lower := by
  have playerEq : boundary.actor.state.player=source := by rw [effect.2]
  rw [playerEq]
  rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> decide +kernel
 have good : OwnedCorral11.Good Front26511.locks Front26511.region boundary.actor.state [265] :=
  ⟨0,heroLower,by decide⟩
 have concatNoNorth : PaidCount11.count FirstRest18711.paid Rest
     (boundary.beforeDirs++boundary.direction::boundary.afterDirs)
     (boundary.beforeOutcomes++boundary.headOutcome::boundary.afterOutcomes)=0 := by
  simpa only [←boundary.dirsEq,←boundary.outcomesEq] using noNorth
 rw [PaidCount11.append boundary.before.logged] at concatNoNorth
 change PaidCount11.count FirstRest18711.paid Rest boundary.beforeDirs boundary.beforeOutcomes+
   ((if PaidCount11.owned FirstRest18711.paid (endGroup Rest boundary.beforeOutcomes) boundary.direction boundary.headOutcome then 1 else 0)+
    PaidCount11.count FirstRest18711.paid (update (endGroup Rest boundary.beforeOutcomes) boundary.headOutcome) boundary.afterDirs boundary.afterOutcomes)=0 at concatNoNorth
 have afterNoNorth : PaidCount11.count FirstRest18711.paid
     (endGroup Rest effectsB) boundary.afterDirs boundary.afterOutcomes=0 := by
  rw [endGroup_append]
  change PaidCount11.count FirstRest18711.paid (update (endGroup Rest boundary.beforeOutcomes) boundary.headOutcome) boundary.afterDirs boundary.afterOutcomes=0
  omega
 rcases first_cut_or_quiet (paid:=Front26511.paid) boundary.after [265] with found|quiet
 ·obtain ⟨cut⟩ := found
  obtain ⟨headSource,owner,headMetadata,pays⟩ := cut.headPaid
  have included := end_subset_selected cut.before.logged afterValid.1 [265] (endGroup Rest effectsB)
    (by decide) afterRest.1 (by simpa using frontOwner) afterRest.2
  change Shaft18711.paid headSource cut.direction at pays
  rcases pays with north|positive
  ·have northPaid : OwnedCorral11.PaidStep FirstRest18711.paid
      (endGroup (endGroup Rest effectsB) cut.beforeOutcomes) cut.direction cut.actor :=
      ⟨headSource,included owner,headMetadata,north⟩
   have counted := PaidCount11.event_le (paid:=FirstRest18711.paid)
     (lastDirs:=cut.afterDirs) (last:=cut.afterOutcomes) cut.before.logged cut.headEffect
     (endGroup Rest effectsB) northPaid
   rw [←cut.dirsEq,←cut.outcomesEq,afterNoNorth] at counted
   omega
  ·rcases positive with side|mate
   ·let globalBoundary := TransportEvents11.FirstCut.extend boundary suffix
    let globalCut := TransportEvents11.FirstCut.extend cut suffix
    have belowGlobal : ∃source,source∈endGroup Rest globalBoundary.beforeOutcomes ∧
       globalBoundary.actor.pushSource=some source ∧
       ((source=264∧globalBoundary.direction=.east)∨(source=266∧globalBoundary.direction=.west)∨(source=291∧globalBoundary.direction=.north)) :=
       ⟨source,sourceOwner,metadata,shape⟩
    exact False.elim (LeadingSideRestTwo11.impossible globalBoundary belowGlobal restCap globalCut
      ⟨headMetadata.trans (congrArg some side.1),side.2⟩)
   ·have goodBefore := PairFirstCut11.quiet_good Front26511.closed Front26511.unique Front26511.size cut.before
      afterValid.1 (by decide) (by simpa using frontActual) (by decide) good firstAfter.trace.holes_sublist.subset
    obtain ⟨i,hero,selected⟩ := goodBefore
    have bounded : (endGroup [265] cut.beforeOutcomes).length≤1 := endGroup_length_le [265] cut.beforeOutcomes
    have member := FrontNoReturn26511.complete i _ bounded selected headSource owner
    have noMate : (266:Cell)∉Front26511.locks i := by
     have checked : (List.finRange 3).all (fun i=>decide ((266:Cell)∉Front26511.locks i))=true := by decide +kernel
     exact of_decide_eq_true (List.all_eq_true.mp checked i (by simp))
    exact False.elim (noMate (mate.1 ▸ member))
 ·exact quiet
#print axioms quiet_after
end Owner1007.ModeCFrontQuiet11
