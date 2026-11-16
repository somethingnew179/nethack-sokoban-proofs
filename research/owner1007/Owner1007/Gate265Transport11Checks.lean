import Owner1007.Gate265Transport11Data
namespace Owner1007.Gate265Transport11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem lower_0 : directionCheck lower .north=true := by decide +kernel
#print axioms lower_0
theorem upper_0 : directionCheck upper .north=true := by decide +kernel
#print axioms upper_0
theorem lower_1 : directionCheck lower .south=true := by decide +kernel
#print axioms lower_1
theorem upper_1 : directionCheck upper .south=true := by decide +kernel
#print axioms upper_1
theorem lower_2 : directionCheck lower .east=true := by decide +kernel
#print axioms lower_2
theorem upper_2 : directionCheck upper .east=true := by decide +kernel
#print axioms upper_2
theorem lower_3 : directionCheck lower .west=true := by decide +kernel
#print axioms lower_3
theorem upper_3 : directionCheck upper .west=true := by decide +kernel
#print axioms upper_3
theorem lower_4 : directionCheck lower .northEast=true := by decide +kernel
#print axioms lower_4
theorem upper_4 : directionCheck upper .northEast=true := by decide +kernel
#print axioms upper_4
theorem lower_5 : directionCheck lower .northWest=true := by decide +kernel
#print axioms lower_5
theorem upper_5 : directionCheck upper .northWest=true := by decide +kernel
#print axioms upper_5
theorem lower_6 : directionCheck lower .southEast=true := by decide +kernel
#print axioms lower_6
theorem upper_6 : directionCheck upper .southEast=true := by decide +kernel
#print axioms upper_6
theorem lower_7 : directionCheck lower .southWest=true := by decide +kernel
#print axioms lower_7
theorem upper_7 : directionCheck upper .southWest=true := by decide +kernel
#print axioms upper_7
end Owner1007.Gate265Transport11
