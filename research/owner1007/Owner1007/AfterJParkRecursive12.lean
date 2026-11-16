import Owner1007.After238210Park12
import Owner1007.After210236Park12
import Owner1007.CageFour12
import Owner1007.After210236Bound12
import Owner1007.After238210Bound12
namespace Owner1007.AfterJParkRecursive12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem after236
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 236 (.stay 262)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 5) (inside : AfterJ12.locks 0 i⊆endGroup group before)
 (prior : endGroup (AfterJ12.ordinary 0) before=AfterJ12.ordinary 0)
 (completed : Goal final) :
 4≤energy p (AfterJ12.ordinary 0) (before++(.push 236 (.stay 262))::after) ∨
 6≤energy p group (before++(.push 236 (.stay 262))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group unique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 236 (.stay 262)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 236 (.stay 262)) effect
   (endGroup group before) old.1 old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have owner : (236 : Cell)∈endGroup group before := inside ((show ∀ i : Fin 5, (236:Cell)∈AfterJ12.locks 0 i from by decide +kernel) i)
 have activation : ∀ i : Fin 5, After21023612.locks i⊆262::(AfterJ12.locks 0 i).erase 236 := by decide +kernel
 have kept := CageFour12.shifted_inside (AfterJ12.unique 0 i) inside owner (activation i)
 have hero : t.state.player∈After21023612.region i := by
   rw [matches_hero middle t (.push 236 (.stay 262)) effect]
   exact of_decide_eq_true (List.all_eq_true.mp
     (show (List.finRange 5).all (fun j=>decide ((236:Cell)∈After21023612.region j))=true by decide +kernel) i (by simp))
 have later := After210236Park12.cash_cases_strong last nextReached completed
   (update (endGroup group before) (.push 236 (.stay 262))) nextUnique nextSubset i hero kept
 change 2≤energy p After21023612.ordinary after ∨
   4≤energy p (update (endGroup group before) (.push 236 (.stay 262))) after at later
 have perm : (update (AfterJ12.ordinary 0) (.push 236 (.stay 262))).Perm After21023612.ordinary := by decide +kernel
 have own : (236:Cell)∈AfterJ12.ordinary 0 := by decide +kernel
 have price : slack p (.push 236 (.stay 262))=2 := by decide +kernel
 have wholeOrd : energy p (AfterJ12.ordinary 0) (before++(.push 236 (.stay 262))::after)=
   ownSlack p (AfterJ12.ordinary 0) before+2+energy p After21023612.ordinary after := by
   rw [energy_at_split,prior]
   simp only [projectedOutcome,if_pos own,price]
   rw [energy_perm p perm after]
 have wholeGroup : energy p group (before++(.push 236 (.stay 262))::after)=
   ownSlack p group before+2+energy p (update (endGroup group before) (.push 236 (.stay 262))) after := by
   rw [energy_at_split]
   simp only [projectedOutcome,if_pos owner,price]
 have nnOrd := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (AfterJ12.ordinary 0)
 have nnGroup := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p (AfterJ12.ordinary 0) before at nnOrd
 change 0≤ownSlack p group before at nnGroup
 rcases later with ordinaryTwo | groupFour
 · exact Or.inl (by omega)
 · exact Or.inr (by omega)
#print axioms after236

theorem after238
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 238 (.stay 264)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 5) (inside : AfterJ12.locks 0 i⊆endGroup group before)
 (prior : endGroup (AfterJ12.ordinary 0) before=AfterJ12.ordinary 0)
 (completed : Goal final) :
 4≤energy p (AfterJ12.ordinary 0) (before++(.push 238 (.stay 264))::after) ∨
 6≤energy p group (before++(.push 238 (.stay 264))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group unique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 238 (.stay 264)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 238 (.stay 264)) effect
   (endGroup group before) old.1 old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have owner : (238 : Cell)∈endGroup group before := inside ((show ∀ i : Fin 5, (238:Cell)∈AfterJ12.locks 0 i from by decide +kernel) i)
 have activation : ∀ i : Fin 5, After23821012.locks i⊆264::(AfterJ12.locks 0 i).erase 238 := by decide +kernel
 have kept := CageFour12.shifted_inside (AfterJ12.unique 0 i) inside owner (activation i)
 have hero : t.state.player∈After23821012.region i := by
   rw [matches_hero middle t (.push 238 (.stay 264)) effect]
   exact of_decide_eq_true (List.all_eq_true.mp
     (show (List.finRange 5).all (fun j=>decide ((238:Cell)∈After23821012.region j))=true by decide +kernel) i (by simp))
 have later := After238210Park12.cash_cases_strong last nextReached completed
   (update (endGroup group before) (.push 238 (.stay 264))) nextUnique nextSubset i hero kept
 change 2≤energy p After23821012.ordinary after ∨
   4≤energy p (update (endGroup group before) (.push 238 (.stay 264))) after at later
 have perm : (update (AfterJ12.ordinary 0) (.push 238 (.stay 264))).Perm After23821012.ordinary := by decide +kernel
 have own : (238:Cell)∈AfterJ12.ordinary 0 := by decide +kernel
 have price : slack p (.push 238 (.stay 264))=2 := by decide +kernel
 have wholeOrd : energy p (AfterJ12.ordinary 0) (before++(.push 238 (.stay 264))::after)=
   ownSlack p (AfterJ12.ordinary 0) before+2+energy p After23821012.ordinary after := by
   rw [energy_at_split,prior]
   simp only [projectedOutcome,if_pos own,price]
   rw [energy_perm p perm after]
 have wholeGroup : energy p group (before++(.push 238 (.stay 264))::after)=
   ownSlack p group before+2+energy p (update (endGroup group before) (.push 238 (.stay 264))) after := by
   rw [energy_at_split]
   simp only [projectedOutcome,if_pos owner,price]
 have nnOrd := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (AfterJ12.ordinary 0)
 have nnGroup := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p (AfterJ12.ordinary 0) before at nnOrd
 change 0≤ownSlack p group before at nnGroup
 rcases later with ordinaryTwo | groupFour
 · exact Or.inl (by omega)
 · exact Or.inr (by omega)
#print axioms after238

theorem after210
 {state middle final : State} {t : Transition}
 {beforeDirs afterDirs history : List Dir} {before after : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves past pastMoves : Nat}
 (first : Logged soko1_2.board state beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 210 (.stay 236)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (group : List Cell) (unique : group.Nodup) (subset : group⊆state.boulders)
 (i : Fin 5) (inside : AfterJ12.locks 1 i⊆endGroup group before)
 (prior : endGroup (AfterJ12.ordinary 1) before=AfterJ12.ordinary 1)
 (completed : Goal final) :
 4≤energy p (AfterJ12.ordinary 1) (before++(.push 210 (.stay 236))::after) ∨
 6≤energy p group (before++(.push 210 (.stay 236))::after) := by
 have stateUnique := reached.boulders_nodup (by decide +kernel)
 have old := first.end_subset stateUnique group unique subset
 have middleReached := reached.append first.trace
 have middleUnique := middleReached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 210 (.stay 236)) effect nextActual
   (endGroup group before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (.push 210 (.stay 236)) effect
   (endGroup group before) old.1 old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have owner : (210 : Cell)∈endGroup group before := inside ((show ∀ i : Fin 5, (210:Cell)∈AfterJ12.locks 1 i from by decide +kernel) i)
 have activation : ∀ i : Fin 5, After23821012.locks i⊆236::(AfterJ12.locks 1 i).erase 210 := by decide +kernel
 have kept := CageFour12.shifted_inside (AfterJ12.unique 1 i) inside owner (activation i)
 have hero : t.state.player∈After23821012.region i := by
   rw [matches_hero middle t (.push 210 (.stay 236)) effect]
   exact of_decide_eq_true (List.all_eq_true.mp
     (show (List.finRange 5).all (fun j=>decide ((210:Cell)∈After23821012.region j))=true by decide +kernel) i (by simp))
 have later := After238210Park12.cash_cases_strong last nextReached completed
   (update (endGroup group before) (.push 210 (.stay 236))) nextUnique nextSubset i hero kept
 change 2≤energy p After23821012.ordinary after ∨
   4≤energy p (update (endGroup group before) (.push 210 (.stay 236))) after at later
 have perm : (update (AfterJ12.ordinary 1) (.push 210 (.stay 236))).Perm After23821012.ordinary := by decide +kernel
 have own : (210:Cell)∈AfterJ12.ordinary 1 := by decide +kernel
 have price : slack p (.push 210 (.stay 236))=2 := by decide +kernel
 have wholeOrd : energy p (AfterJ12.ordinary 1) (before++(.push 210 (.stay 236))::after)=
   ownSlack p (AfterJ12.ordinary 1) before+2+energy p After23821012.ordinary after := by
   rw [energy_at_split,prior]
   simp only [projectedOutcome,if_pos own,price]
   rw [energy_perm p perm after]
 have wholeGroup : energy p group (before++(.push 210 (.stay 236))::after)=
   ownSlack p group before+2+energy p (update (endGroup group before) (.push 210 (.stay 236))) after := by
   rw [energy_at_split]
   simp only [projectedOutcome,if_pos owner,price]
 have nnOrd := first.ownSlack_nonnegative Generated.soko1_2_potential_valid (AfterJ12.ordinary 1)
 have nnGroup := first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p (AfterJ12.ordinary 1) before at nnOrd
 change 0≤ownSlack p group before at nnGroup
 rcases later with ordinaryTwo | groupFour
 · exact Or.inl (by omega)
 · exact Or.inr (by omega)
#print axioms after210
end Owner1007.AfterJParkRecursive12
