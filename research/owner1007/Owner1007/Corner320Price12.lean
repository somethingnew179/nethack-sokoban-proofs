import Owner1007.After265EastFive12
namespace Owner1007.Corner320Price12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
theorem west_zero : pushTargets soko1_2.board 292 .west=[291] ∧
 (1+Generated.soko1_2Potential.boulder 291-Generated.soko1_2Potential.boulder 292 : Int)=0 := by decide +kernel
#print axioms west_zero
end Owner1007.Corner320Price12
