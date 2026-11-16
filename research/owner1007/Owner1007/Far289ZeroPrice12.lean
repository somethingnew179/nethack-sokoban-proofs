import Owner1007.RingAfter12
namespace Owner1007.Far289ZeroPrice12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
theorem east_is_zero : pushTargets soko1_2.board 289 .east=[290] ∧
 (1+Generated.soko1_2Potential.boulder 290-Generated.soko1_2Potential.boulder 289 : Int)=0 := by decide +kernel
#print axioms east_is_zero
end Owner1007.Far289ZeroPrice12
