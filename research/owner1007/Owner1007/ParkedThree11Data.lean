import Owner1007.Parked18811
import Owner1007.PostCuts11
namespace Owner1007.ParkedThree11
open NetHack.Sokoban
def patterns : List (List Cell) := [[139,164,189],[139,138,189],[139,112,189],
 [139,164,190],[139,138,190],[139,112,190],
 [139,138,164],[139,112,164],[139,112,138]]
def locks (i : Fin 9) : List Cell := patterns[i.val]?.getD []
def region (i : Fin 9) : List Cell :=
 if i.val=2 then PostCuts11.without PostCuts11.H [112,113,114,115,116,139,140,141,142,189]
 else Parked18811.region i
abbrev paid := Parked18811.paid
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem size : ∀ i, (locks i).length=3 := by decide +kernel
end Owner1007.ParkedThree11
