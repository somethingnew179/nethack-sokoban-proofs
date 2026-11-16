import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north6_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 6 .north=true := by decide +kernel
theorem north6_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 6 .south=true := by decide +kernel
theorem north6_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 6 .east=true := by decide +kernel
theorem north6_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 6 .west=true := by decide +kernel
theorem north6_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 6 .northEast=true := by decide +kernel
theorem north6_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 6 .northWest=true := by decide +kernel
theorem north6_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 6 .southEast=true := by decide +kernel
theorem north6_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 6 .southWest=true := by decide +kernel
theorem north6_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 6=true := by decide +kernel
theorem north6_tags : tagPart northLocks northRegion northPaid northAllowed 6=true := by decide +kernel
theorem north6 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 6=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north6_north
   | south => exact north6_south
   | east => exact north6_east
   | west => exact north6_west
   | northEast => exact north6_northEast
   | northWest => exact north6_northWest
   | southEast => exact north6_southEast
   | southWest => exact north6_southWest
 · exact north6_push
#print axioms north6
#print axioms north6_tags
end Owner1007.PreCage12
