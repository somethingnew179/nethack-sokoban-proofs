import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north2_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 2 .north=true := by decide +kernel
theorem north2_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 2 .south=true := by decide +kernel
theorem north2_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 2 .east=true := by decide +kernel
theorem north2_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 2 .west=true := by decide +kernel
theorem north2_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 2 .northEast=true := by decide +kernel
theorem north2_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 2 .northWest=true := by decide +kernel
theorem north2_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 2 .southEast=true := by decide +kernel
theorem north2_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 2 .southWest=true := by decide +kernel
theorem north2_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 2=true := by decide +kernel
theorem north2_tags : tagPart northLocks northRegion northPaid northAllowed 2=true := by decide +kernel
theorem north2 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 2=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north2_north
   | south => exact north2_south
   | east => exact north2_east
   | west => exact north2_west
   | northEast => exact north2_northEast
   | northWest => exact north2_northWest
   | southEast => exact north2_southEast
   | southWest => exact north2_southWest
 · exact north2_push
#print axioms north2
#print axioms north2_tags
end Owner1007.PreCage12
