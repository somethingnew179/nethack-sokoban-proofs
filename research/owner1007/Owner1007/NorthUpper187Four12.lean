import Owner1007.UpperAfter187Bound12
import Owner1007.NorthActivation12
namespace Owner1007.NorthUpper187Four12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
/-- The actual early187N head costs2 and preserves another2 for the same
Upper identities. The two charges belong to disjoint temporal segments. -/
theorem upper_four
 {middle final : State} {t : Transition}
 {beforeDirs afterDirs : List Dir} {before after outcomes : List Outcome}
 {beforePushes beforeMoves afterPushes afterMoves : Nat}
 (shape : outcomes=before++(.push 187 (.stay 161))::after)
 (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .north=some t)
 (effect : Matches middle t (.push 187 (.stay 161)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (unchanged : endGroup PreCage12.U before=PreCage12.U) :
 4≤energy p PreCage12.U outcomes := by
 have actualUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have selected := first.end_subset actualUnique PreCage12.U (by decide +kernel) (by decide +kernel)
 have reached := NorthBound12.north_reached.append first.trace
 have middleUnique := reached.boulders_nodup (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ middleUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 187 (.stay 161)) effect nextActual
   (endGroup PreCage12.U before) selected.1 selected.2
 have nextSubset := GhostSubset.update_subset middle t (.push 187 (.stay 161)) effect
   (endGroup PreCage12.U before) selected.1 selected.2
 have owner : (187:Cell)∈endGroup PreCage12.U before := by rw [unchanged]; decide +kernel
 have inside : UpperAfter18712.locks 0⊆update (endGroup PreCage12.U before) (.push 187 (.stay 161)) := by
   rw [unchanged]; decide +kernel
 have hero : t.state.player∈UpperAfter18712.region 0 := by
   rw [matches_hero middle t (.push 187 (.stay 161)) effect]
   exact UpperAfter18712.hero187
 have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
 have later := UpperAfter18712.owned_energy_two UpperAfter18712.matrix last nextReached
   (update (endGroup PreCage12.U before) (.push 187 (.stay 161))) nextUnique nextSubset hero inside
 change 2≤energy p (update (endGroup PreCage12.U before) (.push 187 (.stay 161))) after at later
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid PreCage12.U
 change 0≤ownSlack p PreCage12.U before at nn
 have one : slack p (.push 187 (.stay 161))=2 := by decide +kernel
 rw [shape,energy_at_split]
 simp only [projectedOutcome,if_pos owner,one]
 omega
#print axioms upper_four
end Owner1007.NorthUpper187Four12
