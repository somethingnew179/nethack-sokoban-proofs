import Owner1007.SidecarTwoStage12
import Owner1007.SidecarCriticalBranch12
import Owner1007.After264Pre187Bound12
import Owner1007.LowCoreGate12
import Owner1007.NorthTight22812
namespace Owner1007.SidecarCriticalZero12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12
open Owner1007.SidecarCore12 (locks region)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev stationary211 := @SidecarCriticalBranch12.stationary211

theorem tail_cases
 {final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (zero187 : energy p [187] outcomes=0)
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
 (i : Fin 5) (cashLocks : AfterJ12.locks 1 i⊆middle2.boulders) :
 2≤energy p (Core 2) after ∨5≤energy p (After264Pre187Bound12.Bottom i) after := by
 have zeroWhole : energy p [187] (before++.push 238 (.stay 264)::(between++.push 264 (.stay 290)::after))=0 := by
   simpa only [shape] using zero187
 let lastBeforeCritical := Logged.cons head2 effect2 last
 have initialCore : Core 0⊆FirstSplit12.afterN.boulders := by decide +kernel
 have classified := SidecarTwoStage12.after_first_clearance first head1 effect1 second lastBeforeCritical
   NorthBound12.north_reached initialCore quietBefore quietBetween zeroWhole
 let leadOutcomes := before++.push 238 (.stay 264)::between
 let lead := first.append (Logged.cons head1 effect1 second)
 have beforeReached := NorthBound12.north_reached.append lead.trace
 have beforeUnique := beforeReached.boulders_nodup (by decide +kernel)
 have nextReached := beforeReached.append (Trace.cons head2 (Trace.nil t2.state))
 have nextActual := step_boulders_nodup _ _ _ _ beforeUnique head2
 have allShape : outcomes=leadOutcomes++.push 264 (.stay 290)::after := by
   rw [shape]
   simp only [leadOutcomes,List.append_assoc,List.cons_append]
 have leadOutcomesNN := lead.ownSlack_nonnegative Generated.soko1_2_potential_valid [187]
 change 0≤ownSlack p [187] leadOutcomes at leadOutcomesNN
 have firstMiddleReached := NorthBound12.north_reached.append first.trace
 have firstNextReached := firstMiddleReached.append (Trace.cons head1 (Trace.nil t1.state))
 have initialTag := no_push_unchanged (Core 0) before quietBefore
 have initialPhysical := first.end_subset (by decide +kernel) (Core 0) (core_unique 0) initialCore
 have coreAt : Core 0⊆middle1.boulders := by simpa only [initialTag] using initialPhysical.2
 have firstNextCore := GhostSubset.update_subset middle1 t1 (.push 238 (.stay 264)) effect1
   (Core 0) (core_unique 0) coreAt
 have coreNext : Core 1⊆t1.state.boulders :=
   List.Subset.trans (by decide +kernel : Core 1⊆update (Core 0) (.push 238 (.stay 264))) firstNextCore
 have sQuiet := stationary211 second firstNextReached 1 coreNext quietBetween
 have sTag := no_push_unchanged [211] between sQuiet
 have sPhysical := second.end_subset (firstNextReached.boulders_nodup (by decide +kernel))
   [211] (by decide +kernel) (by simpa using s211)
 have sAt : (211:Cell)∈middle2.boulders := by
   exact sPhysical.2 (show (211:Cell)∈endGroup [211] between by rw [sTag];simp)
 have sNext : (211:Cell)∈t2.state.boulders := by
   have kept := GhostSubset.update_subset middle2 t2 (.push 264 (.stay 290)) effect2 [211]
     (by decide +kernel) (by simpa using sAt)
   have same : update [211] (.push 264 (.stay 290))=[211] := by decide +kernel
   rw [same] at kept
   exact kept (by simp)
 rcases classified with tag187|shifted
 · have laterNN := last.energy_nonnegative Generated.soko1_2_potential_valid [187]
   change 0≤energy p [187] after at laterNN
   have split : energy p [187] outcomes=ownSlack p [187] leadOutcomes+energy p [187] after := by
     rw [allShape,energy_at_split,tag187]
     have absent : (264:Cell)∉([187]:List Cell) := by decide +kernel
     simp only [projectedOutcome,if_neg absent,slack,update,move,if_neg absent,Int.add_zero]
   have zeroTail : energy p [187] after=0 := by omega
   have groupFacts := lead.end_subset (by decide +kernel) [187] (by decide +kernel) (by decide +kernel)
   have at187 : (187:Cell)∈middle2.boulders := by
     exact groupFacts.2 (by rw [tag187];simp)
   have next187 : (187:Cell)∈t2.state.boulders := by
     have kept := GhostSubset.update_subset middle2 t2 (.push 264 (.stay 290)) effect2 [187]
       (by decide +kernel) (by simpa using at187)
     have same : update [187] (.push 264 (.stay 290))=[187] := by decide +kernel
     rw [same] at kept
     exact kept (by simp)
   have cashNext := GhostSubset.update_subset middle2 t2 (.push 264 (.stay 290)) effect2
     (AfterJ12.locks 1 i) (AfterJ12.unique 1 i) cashLocks
   have preInside : After264Pre18712.locks i⊆t2.state.boulders := by
     have check : ∀ i,After264Pre18712.locks i⊆
       update (AfterJ12.locks 1 i) (.push 264 (.stay 290))++[211,187] := by decide +kernel
     intro c member
     rcases List.mem_append.mp (check i member) with old|extra
     · exact cashNext old
     · simp only [List.mem_cons,List.not_mem_nil,or_false] at extra
       rcases extra with same|same
       · simpa only [same] using sNext
       · simpa only [same] using next187
   have nextHero : t2.state.player∈After264Pre18712.region i := by
     rw [matches_hero middle2 t2 (.push 264 (.stay 290)) effect2]
     exact After264Pre18712.hero264 i
   have bound := After264Pre187Bound12.core_two_or_bottom_five last nextReached completed i nextHero preInside zeroTail
   change 2≤energy p (Core 2) after ∨5≤energy p (After264Pre187Bound12.Bottom i) after at bound
   exact bound
 · obtain ⟨tag213,hero213,inside213⟩ := shifted
   have laterNN := last.energy_nonnegative Generated.soko1_2_potential_valid [213]
   change 0≤energy p [213] after at laterNN
   have split : energy p [187] outcomes=ownSlack p [187] leadOutcomes+energy p [213] after := by
     rw [allShape,energy_at_split,tag213]
     have absent : (264:Cell)∉([213]:List Cell) := by decide +kernel
     simp only [projectedOutcome,if_neg absent,slack,update,move,if_neg absent,Int.add_zero]
   have zeroTail : energy p [213] after=0 := by omega
   have kept := GhostSubset.update_subset middle2 t2 (.push 264 (.stay 290)) effect2
     (locks 1) (SidecarCore12.unique 1) inside213
   have lowInside : LowCoreGate12.locks 5⊆t2.state.boulders :=
     List.Subset.trans (by decide +kernel : LowCoreGate12.locks 5⊆update (locks 1) (.push 264 (.stay 290))) kept
   have nextHero : t2.state.player∈LowCoreGate12.region 5 := by
     rw [matches_hero middle2 t2 (.push 264 (.stay 290)) effect2]
     decide +kernel
   have two := LowCoreGate12.energy_two last nextReached completed 5 nextHero lowInside zeroTail
   change 2≤energy p (Core 2) after at two
   exact Or.inl two
#print axioms stationary211
#print axioms tail_cases
end Owner1007.SidecarCriticalZero12
