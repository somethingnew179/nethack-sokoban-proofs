import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north3_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 3 .north=true := by decide +kernel
theorem north3_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 3 .south=true := by decide +kernel
theorem north3_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 3 .east=true := by decide +kernel
theorem north3_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 3 .west=true := by decide +kernel
theorem north3_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 3 .northEast=true := by decide +kernel
theorem north3_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 3 .northWest=true := by decide +kernel
theorem north3_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 3 .southEast=true := by decide +kernel
theorem north3_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 3 .southWest=true := by decide +kernel
theorem north3_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 3=true := by decide +kernel
theorem north3_tags : tagPart northLocks northRegion northPaid northAllowed 3=true := by decide +kernel
theorem north3 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 3=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north3_north
   | south => exact north3_south
   | east => exact north3_east
   | west => exact north3_west
   | northEast => exact north3_northEast
   | northWest => exact north3_northWest
   | southEast => exact north3_southEast
   | southWest => exact north3_southWest
 · exact north3_push
#print axioms north3
#print axioms north3_tags
end Owner1007.PreCage12
