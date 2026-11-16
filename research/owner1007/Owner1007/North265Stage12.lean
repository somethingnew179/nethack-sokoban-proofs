import Owner1007.North22712
namespace Owner1007.North265Stage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north_s212 : ∀ i : Fin 10, ∀ hero∈Owner1007.PreCage12.northRegion i,
 advance soko1_2.board hero .south=some 265 → Owner1007.PreCage12.northS i=212 := by decide +kernel
#print axioms north_s212
end Owner1007.North265Stage12
