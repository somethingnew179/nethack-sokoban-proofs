import Owner1007.AboveOther11Node0
import Owner1007.AboveOther11Node1
import Owner1007.AboveOther11Node2
namespace Owner1007.AboveOther11
open NetHack.Sokoban

theorem checked (i : Fin 3) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1∨i=2 := by omega
 rcases choices with rfl|rfl|rfl
 ·exact matrix0
 ·exact matrix1
 ·exact matrix2

theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor checked
#print axioms closed
end Owner1007.AboveOther11
