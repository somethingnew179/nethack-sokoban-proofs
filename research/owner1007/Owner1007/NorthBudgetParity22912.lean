import Owner1007.NorthParityPrice12
import Owner1007.North318Bound12
namespace Owner1007.NorthBudgetParity22912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev Left := NorthParityPrice12.Left
theorem left_le_twelve {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤229) :energy p Left outcomes≤12 := by
 by_cases small:energy p Left outcomes≤12
 ·exact small
 ·have lower:13≤energy p Left outcomes:=by omega
  have impossible:=NorthParityPrice12.thirteen_implies_230 logged completed lower
  omega
theorem current_tag {state dirs pushes moves outcomes}
 (first : Logged soko1_2.board FirstSplit12.afterN dirs state pushes moves outcomes)
 (i : Fin 5) (inside : NorthEvents12.locks i⊆endGroup NorthBound12.G outcomes)
 (fixed : ∀small:List Cell,small⊆NorthEvents12.J→endGroup small outcomes=small) :
 endGroup [345] outcomes=[NorthEvents12.current i] := by
 have split:=first.end_split (show FirstSplit12.afterN.boulders.Nodup by decide +kernel)
   NorthEvents12.J [345] (by decide +kernel) (by decide +kernel)
 change (endGroup NorthEvents12.J outcomes++endGroup [345] outcomes).Perm (endGroup NorthBound12.G outcomes) at split
 rw[fixed NorthEvents12.J (fun _ h=>h)] at split
 exact North318Bound12.singleton_complement NorthEvents12.J (endGroup [345] outcomes)
   (endGroup NorthBound12.G outcomes) (NorthEvents12.current i) split
   (inside (North318Bound12.current_member i)) (North318Bound12.current_away i)
   (by have bound:=endGroup_length_le [345] outcomes;simpa using bound)
#print axioms left_le_twelve
#print axioms current_tag
end Owner1007.NorthBudgetParity22912
