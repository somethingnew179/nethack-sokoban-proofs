import Owner1007.LowerTrap31819Data
namespace Owner1007.LowerTrap31819
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checked0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 0=true := by decide +kernel
theorem checked1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid 1=true := by decide +kernel
theorem checked (i : Fin 2) : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid i=true := by
 obtain ⟨v,bound⟩ := i
 have choices : v=0∨v=1 := by omega
 rcases choices with rfl|rfl
 · exact checked0
 · exact checked1
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid :=
 FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor checked
#print axioms checked
#print axioms closed
end Owner1007.LowerTrap31819
