import Owner1007.NorthAfterJPark23112
import Owner1007.NorthFirstJ22812
namespace Owner1007.NorthFirstJParkFacts12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem bottom_cases {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cut : NorthFirstJ22812.FirstJ final outcomes)
 {betweenDirs middle betweenPushes betweenMoves between t afterDirs afterPushes afterMoves after}
 (shape : cut.after=between++.push 318 (.stay 317)::after)
 (gap : Logged soko1_2.board cut.actor.state betweenDirs middle betweenPushes betweenMoves between)
 (head : step soko1_2.board middle .west=some t) (effect : Matches middle t (.push 318 (.stay 317)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (i : Fin 5) (hero : middle.player∈AfterJ12.region cut.kind i)
 (locks : AfterJ12.locks cut.kind i⊆endGroup (update (endGroup NorthBound12.G cut.before) (AfterJBound12.headOutcome cut.kind)) between)
 (fixed : ∀small : List Cell,small⊆AfterJ12.fixed cut.kind→endGroup small between=small) :
 7≤energy p NorthBound12.BottomN outcomes∧endGroup [318] outcomes≠[]∧endGroup [345] outcomes≠[] := by
 let before := cut.before++AfterJBound12.headOutcome cut.kind::between
 let lead := cut.first.append (Logged.cons cut.checked cut.effect gap)
 have shapeWhole : outcomes=before++.push 318 (.stay 317)::after := by
  rw[cut.shape,shape]
  simp only[before,List.append_assoc,List.cons_append]
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have fixedJ:=cut.fixedBefore NorthEvents12.J (fun _ h=>h)
 have shiftedJ : (update NorthEvents12.J (AfterJBound12.headOutcome cut.kind)).Perm (AfterJ12.fixed cut.kind) := by
  have checked : ∀kind:Fin 2,(update NorthEvents12.J (AfterJBound12.headOutcome kind)).Perm (AfterJ12.fixed kind) := by decide +kernel
  exact checked cut.kind
 have atJ : (endGroup NorthEvents12.J before).Perm (AfterJ12.fixed cut.kind) := by
  simp only[before,endGroup_append,fixedJ,endGroup]
  have same:=endGroup_perm shiftedJ between
  rw[fixed (AfterJ12.fixed cut.kind) (fun _ h=>h)] at same
  exact same
 have split:=lead.end_split initialUnique NorthEvents12.J [345] (by decide +kernel) (by decide +kernel)
 change (endGroup NorthEvents12.J before++endGroup [345] before).Perm (endGroup NorthBound12.G before) at split
 have known : (AfterJ12.fixed cut.kind++endGroup [345] before).Perm (endGroup NorthBound12.G before) :=
  (atJ.symm.append_right _).trans split
 have currentMember : NorthEvents12.current i∈endGroup NorthBound12.G before := by
  have check : ∀kind:Fin 2,∀i,NorthEvents12.current i∈AfterJ12.locks kind i := by decide +kernel
  have member:=locks (check cut.kind i)
  simpa only[before,endGroup_append,endGroup] using member
 have away : NorthEvents12.current i∉AfterJ12.fixed cut.kind := by
  have check : ∀kind:Fin 2,∀i,NorthEvents12.current i∉AfterJ12.fixed kind := by decide +kernel
  exact check cut.kind i
 have prior345:=North318Bound12.singleton_complement (AfterJ12.fixed cut.kind) (endGroup [345] before)
  (endGroup NorthBound12.G before) (NorthEvents12.current i) known currentMember away
  (by have bound:=endGroup_length_le [345] before;simpa using bound)
 have prior318 : endGroup [318] before=[318] := by
  have original:=cut.fixedBefore [318] (by decide +kernel)
  have shifted : ∀kind:Fin 2,update [318] (AfterJBound12.headOutcome kind)=[318] := by decide +kernel
  simp only[before,endGroup_append,original,endGroup,shifted]
  have member : ∀kind:Fin 2,([318]:List Cell)⊆AfterJ12.fixed kind := by decide +kernel
  exact fixed [318] (member cut.kind)
 have bottom:=NorthAfterJPark23112.bottom_cases logged shapeWhole lead head effect last cut.kind i hero prior318 prior345
 exact bottom
#print axioms bottom_cases
end Owner1007.NorthFirstJParkFacts12
