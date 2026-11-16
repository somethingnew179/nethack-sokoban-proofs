import Owner1007.CriticalWithout187Seven12
import Owner1007.NorthAfterFirstQuietTen12
import Owner1007.SidecarCriticalBranch12
import Owner1007.NorthParityPrice23212
import Owner1007.LeftQuietIdentity11
namespace Owner1007.NorthCritical23212
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12 (Core core_unique)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev GS := NorthActivation12.GS

theorem critical_lower232 {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cut : NorthFirstJ22812.FirstJ final outcomes)
 (critical : NorthAfterFirstTen12.Critical264 cut)
 (quiet : ownPushes (AfterJ12.fixed cut.kind) critical.between=0) : 232≤1+pushes := by
 have kindEq:=critical.kindEq
 have firstHead : AfterJBound12.headOutcome cut.kind=.push 238 (.stay 264) := by rw[kindEq];rfl
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have firstReached:=NorthBound12.north_reached.append cut.first.trace
 have firstEffect : Matches cut.middle cut.actor (.push 238 (.stay 264)) := by simpa only[firstHead] using cut.effect
 have afterFirstReached:=firstReached.append (Trace.cons cut.checked (Trace.nil cut.actor.state))
 have coreTag:=cut.fixedBefore (Core 0) (by decide +kernel)
 have corePhysical:=cut.first.end_subset initialUnique (Core 0) (core_unique 0) (by decide +kernel)
 have coreAt : Core 0⊆cut.middle.boulders := by simpa only[coreTag] using corePhysical.2
 have coreNext:=GhostSubset.update_subset cut.middle cut.actor (.push 238 (.stay 264)) firstEffect (Core 0) (core_unique 0) coreAt
 have core1 : Core 1⊆cut.actor.state.boulders := List.Subset.trans
  (by decide +kernel : Core 1⊆update (Core 0) (.push 238 (.stay 264))) coreNext
 have quietCore : ownPushes (Core 1) critical.between=0 := by
  apply LeftQuietIdentity11.subset_zero (Core 1) (AfterJ12.fixed cut.kind) critical.between
  ·rw[kindEq];decide +kernel
  ·exact quiet
 have quietS:=SidecarCriticalBranch12.stationary211 critical.gap afterFirstReached 1 core1 quietCore
 have keptS : endGroup [211] critical.between=[211] := no_push_unchanged _ _ quietS
 let before := cut.before++AfterJBound12.headOutcome cut.kind::critical.between
 let lead:=cut.first.append (Logged.cons cut.checked cut.effect critical.gap)
 have sBefore : endGroup [213] before=[211] := by
  simp only[before,endGroup_append,cut.sAt,endGroup,firstHead]
  have same : update [211] (.push 238 (.stay 264))=[211] := by decide +kernel
  rw[same]
  exact keptS
 have gLocks : AfterJ12.locks 1 critical.phase⊆endGroup NorthBound12.G before := by
  have same:=critical.locks
  rw[kindEq] at same
  simpa only[before,endGroup_append,endGroup,kindEq] using same
 have groupUnique : GS.Nodup := by decide +kernel
 have groupSubset : GS⊆FirstSplit12.afterN.boulders := by decide +kernel
 have split:=lead.end_split initialUnique NorthBound12.G [213] groupUnique groupSubset
 change (endGroup NorthBound12.G before++endGroup [213] before).Perm (endGroup GS before) at split
 rw[sBefore] at split
 have retained : AfterJ12.locks 1 critical.phase++[211]⊆endGroup GS before := by
  intro c member
  apply split.mem_iff.mp
  rcases List.mem_append.mp member with core|marker
  ·exact List.mem_append_left _ (gLocks core)
  ·exact List.mem_append_right _ marker
 have ownerG : (264:Cell)∈endGroup NorthBound12.G before := by
  apply gLocks
  have check : ∀i,(264:Cell)∈AfterJ12.locks 1 i := by decide +kernel
  exact check critical.phase
 have ownerGS : (264:Cell)∈endGroup GS before := split.mem_iff.mp (List.mem_append_left _ ownerG)
 have atReached:=NorthBound12.north_reached.append lead.trace
 have facts:=lead.end_subset initialUnique GS groupUnique groupSubset
 have nextActual:=step_boulders_nodup _ _ _ _ (atReached.boulders_nodup (by decide +kernel)) critical.checked
 have nextUnique:=GhostSubset.update_unique _ _ _ critical.effect nextActual _ facts.1 facts.2
 have nextSubset:=GhostSubset.update_subset _ _ _ critical.effect _ facts.1 facts.2
 have nextReached:=atReached.append (Trace.cons critical.checked (Trace.nil critical.actor.state))
 have oldUnique : ∀i,(AfterJ12.locks 1 i++[211]).Nodup := by decide +kernel
 have shift : ∀i,CriticalWithout18712.locks i⊆290::(AfterJ12.locks 1 i++[211]).erase 264 := by decide +kernel
 have current:=CageFour12.shifted_inside (oldUnique critical.phase) retained ownerGS (shift critical.phase)
 have hero : critical.actor.state.player∈CriticalWithout18712.region critical.phase := by
  rw[matches_hero critical.middle critical.actor (.push 264 (.stay 290)) critical.effect]
  exact CriticalWithout18712.hero264 critical.phase
 have seven:=CriticalWithout187Seven12.energy_seven critical.last nextReached
  (update (endGroup GS before) (.push 264 (.stay 290))) nextUnique nextSubset completed hero current
 change 7≤energy p (update (endGroup GS before) (.push 264 (.stay 290))) critical.after at seven
 have firstOwnerG : AfterJBound12.startSource cut.kind∈endGroup NorthBound12.G cut.before :=
  cut.locks (AfterJBound12.source_inside cut.kind cut.phase)
 have mono:=cut.first.end_mono initialUnique NorthBound12.G GS (by decide +kernel) (by decide +kernel) (by decide +kernel)
 have firstOwnerGS:=mono firstOwnerG
 have nn0:=cut.first.ownSlack_nonnegative Generated.soko1_2_potential_valid GS
 have nn1:=critical.gap.ownSlack_nonnegative Generated.soko1_2_potential_valid
  (update (endGroup GS cut.before) (AfterJBound12.headOutcome cut.kind))
 change 0≤ownSlack p GS cut.before at nn0
 change 0≤ownSlack p (update (endGroup GS cut.before) (AfterJBound12.headOutcome cut.kind)) critical.between at nn1
 have prefixTwo : 2≤ownSlack p GS before := by
  change 2≤ownSlack p GS (cut.before++AfterJBound12.headOutcome cut.kind::critical.between)
  rw[ownSlack_append,ownSlack]
  have own : projectedOutcome (endGroup GS cut.before) (AfterJBound12.headOutcome cut.kind)=AfterJBound12.headOutcome cut.kind := by
   simp only[AfterJBound12.headOutcome,projectedOutcome,if_pos firstOwnerGS]
  rw[own,AfterJBound12.first_price]
  omega
 have shapeWhole : outcomes=before++.push 264 (.stay 290)::critical.after := by
  calc
   outcomes=cut.before++AfterJBound12.headOutcome cut.kind::cut.after := cut.shape
   _=cut.before++AfterJBound12.headOutcome cut.kind::(critical.between++.push 264 (.stay 290)::critical.after) :=
    congrArg (fun rest=>cut.before++AfterJBound12.headOutcome cut.kind::rest) critical.shape
   _=before++.push 264 (.stay 290)::critical.after := by simp only[before,List.append_assoc,List.cons_append]
 have ledger:=energy_at_split p GS before (.push 264 (.stay 290)) critical.after
 have price : slack p (.push 264 (.stay 290))=4 := by decide +kernel
 simp only[projectedOutcome,if_pos ownerGS,price] at ledger
 rw[←shapeWhole] at ledger
 have thirteen : 13≤energy p GS outcomes := by omega
 have upper:=RightEnergy12.raw_group_energy logged NorthBound12.north_reached PreCage12.U
  (by decide +kernel) (by decide +kernel) completed
 have bonus : RightEnergy12.cert.bonus FirstSplit12.afterN.player (PatternCorrection.project PreCage12.U)=2 := by decide +kernel
 rw[bonus] at upper
 change 2≤energy p PreCage12.U outcomes at upper
 have leftSplit:=logged.energy_split initialUnique p PreCage12.U GS (by decide +kernel) (by decide +kernel)
 change energy p NorthPriceBalance12.Left outcomes=energy p PreCage12.U outcomes+energy p GS outcomes at leftSplit
 have fifteen : 15≤energy p NorthPriceBalance12.Left outcomes := by omega
 exact NorthParityPrice23212.fifteen_implies_232 logged completed fifteen
#print axioms critical_lower232
end Owner1007.NorthCritical23212
