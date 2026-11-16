import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north9_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 9 .north=true := by decide +kernel
theorem north9_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 9 .south=true := by decide +kernel
theorem north9_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 9 .east=true := by decide +kernel
theorem north9_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 9 .west=true := by decide +kernel
theorem north9_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 9 .northEast=true := by decide +kernel
theorem north9_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 9 .northWest=true := by decide +kernel
theorem north9_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 9 .southEast=true := by decide +kernel
theorem north9_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 9 .southWest=true := by decide +kernel
theorem north9_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 9=true := by decide +kernel
theorem north9_tags : tagPart northLocks northRegion northPaid northAllowed 9=true := by decide +kernel
theorem north9 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 9=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north9_north
   | south => exact north9_south
   | east => exact north9_east
   | west => exact north9_west
   | northEast => exact north9_northEast
   | northWest => exact north9_northWest
   | southEast => exact north9_southEast
   | southWest => exact north9_southWest
 · exact north9_push
#print axioms north9
#print axioms north9_tags
end Owner1007.PreCage12
