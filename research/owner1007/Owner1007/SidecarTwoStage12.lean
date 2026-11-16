import Owner1007.Sidecar187Classify12
namespace Owner1007.SidecarTwoStage12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12
open Owner1007.SidecarCore12 (locks region)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem after_first_clearance
 {state middle1 t middle2 final dirs1 dirs2 dirs3 pushes1 moves1 pushes2 moves2 pushes3 moves3 before between after}
 (first : Logged soko1_2.board state dirs1 middle1 pushes1 moves1 before)
 (head : step soko1_2.board middle1 .south=some t)
 (effect : Matches middle1 t (.push 238 (.stay 264)))
 (second : Logged soko1_2.board t.state dirs2 middle2 pushes2 moves2 between)
 (last : Logged soko1_2.board middle2 dirs3 final pushes3 moves3 after)
 {history : List Dir} {past pastMoves : Nat}
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (coreInside : Core 0⊆state.boulders)
 (quietBefore : ownPushes (Core 0) before=0)
 (quietBetween : ownPushes (Core 1) between=0)
 (zero187 : energy p [187] (before++.push 238 (.stay 264)::(between++after))=0) :
 endGroup [187] (before++.push 238 (.stay 264)::between)=[187] ∨
 (endGroup [187] (before++.push 238 (.stay 264)::between)=[213] ∧
 middle2.player∈region 1 ∧locks 1⊆middle2.boulders) := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextReached := middleReached.append (Trace.cons head (Trace.nil t.state))
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique head
 have tagCore := no_push_unchanged (Core 0) before quietBefore
 have physicalBefore := first.end_subset actualUnique (Core 0) (core_unique 0) coreInside
 have coreAt : Core 0⊆middle1.boulders := by simpa only [tagCore] using physicalBefore.2
 have nextCore := GhostSubset.update_subset middle1 t (.push 238 (.stay 264)) effect
   (Core 0) (core_unique 0) coreAt
 have physicalCore1 : Core 1⊆t.state.boulders := by
   have check : Core 1⊆update (Core 0) (.push 238 (.stay 264)) := by decide +kernel
   exact List.Subset.trans check nextCore
 let tail := Logged.cons head effect (second.append last)
 rcases Sidecar187Classify12.classify first tail reached 0 coreInside quietBefore zero187 with unshifted|shifted
 · have oneNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [187]
   change 0≤ownSlack p [187] before at oneNN
   have suffixNN := (second.append last).energy_nonnegative Generated.soko1_2_potential_valid [187]
   change 0≤energy p [187] (between++after) at suffixNN
   have split : energy p [187] (before++.push 238 (.stay 264)::(between++after))=
       ownSlack p [187] before+energy p [187] (between++after) := by
     rw [energy_at_split,unshifted]
     have notOwn : (238:Cell)∉([187]:List Cell) := by decide +kernel
     simp only [projectedOutcome,if_neg notOwn,slack,update,move,if_neg notOwn,Int.add_zero]
   have zeroLater : energy p [187] (between++after)=0 := by omega
   rcases Sidecar187Classify12.classify second last nextReached 1 physicalCore1 quietBetween zeroLater with same|now
   · exact Or.inl (by
       rw [endGroup_append,unshifted]
       change endGroup [187] between=[187]
       exact same)
   · obtain ⟨tag,hero,inside⟩ := now
     exact Or.inr ⟨by
       rw [endGroup_append,unshifted]
       change endGroup [187] between=[213]
       exact tag,hero,inside⟩
 · obtain ⟨tag213,heroBefore,insideBefore⟩ := shifted
   have oneNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid [187]
   change 0≤ownSlack p [187] before at oneNN
   have suffixNN := (second.append last).energy_nonnegative Generated.soko1_2_potential_valid [213]
   change 0≤energy p [213] (between++after) at suffixNN
   have split : energy p [187] (before++.push 238 (.stay 264)::(between++after))=
       ownSlack p [187] before+energy p [213] (between++after) := by
     rw [energy_at_split,tag213]
     have notOwn : (238:Cell)∉([213]:List Cell) := by decide +kernel
     simp only [projectedOutcome,if_neg notOwn,slack,update,move,if_neg notOwn,Int.add_zero]
   have zeroLater : energy p [213] (between++after)=0 := by omega
   have next213 : (213:Cell)∈t.state.boulders := by
     have present : (213:Cell)∈middle1.boulders := insideBefore (by decide +kernel)
     have next := GhostSubset.update_subset middle1 t (.push 238 (.stay 264)) effect
       [213] (by decide +kernel) (by simpa using present)
     have same : update [213] (.push 238 (.stay 264))=[213] := by decide +kernel
     rw [same] at next
     exact next (by simp)
   have insideNext : locks 1⊆t.state.boulders := by
     have check : locks 1⊆Core 1++[213] := by decide +kernel
     intro c found
     rcases List.mem_append.mp (check found) with core|single
     · exact physicalCore1 core
     · have same : c=213 := List.mem_singleton.mp single
       simpa only [same] using next213
   have heroNext : t.state.player∈region 1 := by
     rw [matches_hero middle1 t (.push 238 (.stay 264)) effect]
     decide +kernel
   obtain ⟨heroFinal,locksFinal,tagFinal⟩ := quiet_prefix_good second last nextReached
     1 heroNext insideNext quietBetween zeroLater
   exact Or.inr ⟨by
     rw [endGroup_append,tag213]
     change endGroup [213] between=[213]
     exact tagFinal,heroFinal,locksFinal⟩
#print axioms after_first_clearance
end Owner1007.SidecarTwoStage12
