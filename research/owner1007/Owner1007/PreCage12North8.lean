import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north8_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 8 .north=true := by decide +kernel
theorem north8_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 8 .south=true := by decide +kernel
theorem north8_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 8 .east=true := by decide +kernel
theorem north8_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 8 .west=true := by decide +kernel
theorem north8_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 8 .northEast=true := by decide +kernel
theorem north8_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 8 .northWest=true := by decide +kernel
theorem north8_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 8 .southEast=true := by decide +kernel
theorem north8_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 8 .southWest=true := by decide +kernel
theorem north8_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 8=true := by decide +kernel
theorem north8_tags : tagPart northLocks northRegion northPaid northAllowed 8=true := by decide +kernel
theorem north8 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 8=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north8_north
   | south => exact north8_south
   | east => exact north8_east
   | west => exact north8_west
   | northEast => exact north8_northEast
   | northWest => exact north8_northWest
   | southEast => exact north8_southEast
   | southWest => exact north8_southWest
 · exact north8_push
#print axioms north8
#print axioms north8_tags
end Owner1007.PreCage12
