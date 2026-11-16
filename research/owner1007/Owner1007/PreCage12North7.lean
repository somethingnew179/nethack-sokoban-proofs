import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north7_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 7 .north=true := by decide +kernel
theorem north7_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 7 .south=true := by decide +kernel
theorem north7_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 7 .east=true := by decide +kernel
theorem north7_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 7 .west=true := by decide +kernel
theorem north7_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 7 .northEast=true := by decide +kernel
theorem north7_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 7 .northWest=true := by decide +kernel
theorem north7_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 7 .southEast=true := by decide +kernel
theorem north7_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 7 .southWest=true := by decide +kernel
theorem north7_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 7=true := by decide +kernel
theorem north7_tags : tagPart northLocks northRegion northPaid northAllowed 7=true := by decide +kernel
theorem north7 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 7=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north7_north
   | south => exact north7_south
   | east => exact north7_east
   | west => exact north7_west
   | northEast => exact north7_northEast
   | northWest => exact north7_northWest
   | southEast => exact north7_southEast
   | southWest => exact north7_southWest
 · exact north7_push
#print axioms north7
#print axioms north7_tags
end Owner1007.PreCage12
