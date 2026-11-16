import Owner1007.LowerTrap31911Data
namespace Owner1007.LowerTrap31911
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem checked (i : Fin 1) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 have same : i=0 := Fin.ext (by have bound:=i.isLt; omega)
 simpa only [same] using checked0
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor checked
#print axioms checked0
#print axioms closed
end Owner1007.LowerTrap31911
