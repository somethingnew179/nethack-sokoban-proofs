import Owner1007.InwardMarkedStart11Check00
import Owner1007.InwardMarkedStart11Check01
import Owner1007.InwardMarkedStart11Check02
import Owner1007.InwardMarkedStart11Check03
import Owner1007.InwardMarkedStart11Check04
import Owner1007.InwardMarkedStart11Check05
import Owner1007.InwardMarkedStart11Check06
import Owner1007.InwardMarkedStart11Check07
namespace Owner1007.InwardMarkedStart11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem checked (i : Fin 8) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true:=by
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7:=by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
 ·exact node3
 ·exact node4
 ·exact node5
 ·exact node6
 ·exact node7
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid:=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor checked
theorem phase_closed (i : Fin 8) :
 PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes
 (fun _ : Fin 1=>locks i) (fun _ : Fin 1=>region i) paid:=by
 constructor
 ·intro j hero member dir target adjacent isFloor door notLock corner
  exact closed.1 i hero member dir target adjacent isFloor door notLock corner
 ·intro j hero member dir source owner adjacent
  exact Or.inr (Or.inl trivial)
theorem head_shape {state : State} {dir : Dir} {t : Transition} {source : Cell}
 (i : Fin 8) (hero : state.player∈region i) (member : source∈locks i) (inside : locks i⊆state.boulders)
 (checked : step soko1_1.board state dir=some t) (metadata : t.pushSource=some source) :
 LeftInwardStart11.Shape source dir:=by
 have row:=List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp heads i (by simp)) source member) dir (Geometry.all_directions dir)
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player (floor i hero) dir source (PairPost11.source_adjacent checked metadata)
 simp only [headCheck,behind] at row
 exact of_decide_eq_true row hero (WestRankHead11.source_unblocked checked metadata inside)
#print axioms closed
#print axioms phase_closed
#print axioms head_shape
end Owner1007.InwardMarkedStart11
