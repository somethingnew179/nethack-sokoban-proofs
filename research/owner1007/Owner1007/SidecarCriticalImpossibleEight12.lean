import Owner1007.SidecarCriticalZero12
import Owner1007.EndGroupMono
namespace Owner1007.SidecarCriticalImpossibleEight12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem impossible
 {final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (gBudget : energy p NorthBound12.G outcomes≤8) (zero187 : energy p [187] outcomes=0)
 {d1 p1 m1 before middle1 t1 d2 p2 m2 between middle2 t2 d3 p3 m3 after}
 (shape : outcomes=before++.push 238 (.stay 264)::(between++.push 264 (.stay 290)::after))
 (first : Logged soko1_2.board FirstSplit12.afterN d1 middle1 p1 m1 before)
 (head1 : step soko1_2.board middle1 .south=some t1)
 (effect1 : Matches middle1 t1 (.push 238 (.stay 264)))
 (second : Logged soko1_2.board t1.state d2 middle2 p2 m2 between)
 (head2 : step soko1_2.board middle2 .south=some t2)
 (effect2 : Matches middle2 t2 (.push 264 (.stay 290)))
 (last : Logged soko1_2.board t2.state d3 final p3 m3 after)
 (quietBefore : ownPushes (Core 0) before=0)
 (quietBetween : ownPushes (Core 1) between=0)
 (s211 : (211:Cell)∈t1.state.boulders)
 (i : Fin 5) (cashLocks : AfterJ12.locks 1 i⊆
   endGroup NorthBound12.G (before++.push 238 (.stay 264)::between)) : False := by
 have actualUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 let leadOutcomes := before++.push 238 (.stay 264)::between
 let lead := first.append (Logged.cons head1 effect1 second)
 have beforeReached := NorthBound12.north_reached.append lead.trace
 have beforeUnique := beforeReached.boulders_nodup (by decide +kernel)
 have groupFacts := lead.end_subset actualUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
 have physicalLocks := List.Subset.trans cashLocks groupFacts.2
 have laterCases := SidecarCriticalZero12.tail_cases logged completed zero187 shape first head1 effect1
   second head2 effect2 last quietBefore quietBetween s211 i physicalLocks
 have gEight := gBudget
 have tag0 := no_push_unchanged (Core 0) before quietBefore
 have tag1 := no_push_unchanged (Core 1) between quietBetween
 have firstPrice : slack p (.push 238 (.stay 264))=2 := by decide +kernel
 have secondPrice : slack p (.push 264 (.stay 290))=4 := by decide +kernel
 have owner0 : (238:Cell)∈Core 0 := by decide +kernel
 have owner1 : (264:Cell)∈Core 1 := by decide +kernel
 have shift1 : (update (Core 0) (.push 238 (.stay 264))).Perm (Core 1) := by decide +kernel
 have shift2 : (update (Core 1) (.push 264 (.stay 290))).Perm (Core 2) := by decide +kernel
 have nn0 := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (Core 0)
 have nn1 := second.ownSlack_nonnegative Generated.soko1_2_potential_valid (Core 1)
 change 0≤ownSlack p (Core 0) before at nn0
 change 0≤ownSlack p (Core 1) between at nn1
 have coreLedger : energy p (Core 0) outcomes=
     ownSlack p (Core 0) before+2+ownSlack p (Core 1) between+4+energy p (Core 2) after := by
   rw [shape,energy_at_split,tag0]
   simp only [projectedOutcome,if_pos owner0,firstPrice]
   rw [energy_perm p shift1,energy_at_split,tag1]
   simp only [projectedOutcome,if_pos owner1,secondPrice]
   rw [energy_perm p shift2]
   omega
 rcases laterCases with coreTwo|bottomFive
 · have coreHigh : 8≤energy p (Core 0) outcomes := by omega
   have coreJ : (Core 0).Perm NorthBound12.J := by decide +kernel
   rw [energy_perm p coreJ] at coreHigh
   have bottom := NorthBound12.bottom_north_energy_two logged
   change 2≤energy p NorthBound12.BottomN outcomes at bottom
   have gSplit := logged.energy_split actualUnique p NorthBound12.J NorthBound12.BottomN
     (by decide +kernel) (by decide +kernel)
   change energy p NorthBound12.G outcomes=energy p NorthBound12.J outcomes+energy p NorthBound12.BottomN outcomes at gSplit
   omega
 · have nextActual := step_boulders_nodup _ _ _ _ beforeUnique head2
   have nextUnique := GhostSubset.update_unique middle2 t2 (.push 264 (.stay 290)) effect2 nextActual
     (endGroup NorthBound12.G leadOutcomes) groupFacts.1 groupFacts.2
   have nextSubset := GhostSubset.update_subset middle2 t2 (.push 264 (.stay 290)) effect2
     (endGroup NorthBound12.G leadOutcomes) groupFacts.1 groupFacts.2
   have ownerG2 : (264:Cell)∈endGroup NorthBound12.G leadOutcomes := by
     have all : ∀ i,(264:Cell)∈AfterJ12.locks 1 i := by decide +kernel
     exact cashLocks (all i)
   have bottomShift : ∀ i,After264Pre187Bound12.Bottom i⊆
       290::(AfterJ12.locks 1 i).erase 264 := by decide +kernel
   have bottomInside := CageFour12.shifted_inside (AfterJ12.unique 1 i) cashLocks ownerG2 (bottomShift i)
   have bottomUnique : (After264Pre187Bound12.Bottom i).Nodup := by
     have all : ∀ i,(After264Pre187Bound12.Bottom i).Nodup := by decide +kernel
     exact all i
   have larger := last.energy_mono Generated.soko1_2_potential_valid nextActual
     (After264Pre187Bound12.Bottom i) (update (endGroup NorthBound12.G leadOutcomes) (.push 264 (.stay 290)))
     bottomUnique nextUnique (List.Subset.trans bottomInside nextSubset) nextSubset bottomInside
   change energy p (After264Pre187Bound12.Bottom i) after≤
     energy p (update (endGroup NorthBound12.G leadOutcomes) (.push 264 (.stay 290))) after at larger
   have endMono := first.end_mono actualUnique (Core 0) NorthBound12.G (core_unique 0)
     (by decide +kernel) (by decide +kernel)
   have ownerG1 : (238:Cell)∈endGroup NorthBound12.G before := by
     apply endMono
     rw [tag0]
     exact owner0
   have nnBefore := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.G
   have nnBetween := second.ownSlack_nonnegative Generated.soko1_2_potential_valid
     (update (endGroup NorthBound12.G before) (.push 238 (.stay 264)))
   change 0≤ownSlack p NorthBound12.G before at nnBefore
   change 0≤ownSlack p (update (endGroup NorthBound12.G before) (.push 238 (.stay 264))) between at nnBetween
   have prefixBound : 2≤ownSlack p NorthBound12.G leadOutcomes := by
     simp only [leadOutcomes,ownSlack_append,ownSlack]
     simp only [projectedOutcome,if_pos ownerG1,firstPrice]
     omega
   have allShape : outcomes=leadOutcomes++.push 264 (.stay 290)::after := by
     rw [shape]
     simp only [leadOutcomes,List.append_assoc,List.cons_append]
   have gLedger := energy_at_split p NorthBound12.G leadOutcomes (.push 264 (.stay 290)) after
   rw [←allShape] at gLedger
   simp only [projectedOutcome,if_pos ownerG2,secondPrice] at gLedger
   omega
#print axioms impossible
end Owner1007.SidecarCriticalImpossibleEight12
