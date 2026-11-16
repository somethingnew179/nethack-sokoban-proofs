import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north5_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 5 .north=true := by decide +kernel
theorem north5_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 5 .south=true := by decide +kernel
theorem north5_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 5 .east=true := by decide +kernel
theorem north5_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 5 .west=true := by decide +kernel
theorem north5_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 5 .northEast=true := by decide +kernel
theorem north5_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 5 .northWest=true := by decide +kernel
theorem north5_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 5 .southEast=true := by decide +kernel
theorem north5_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 5 .southWest=true := by decide +kernel
theorem north5_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 5=true := by decide +kernel
theorem north5_tags : tagPart northLocks northRegion northPaid northAllowed 5=true := by decide +kernel
theorem north5 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 5=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north5_north
   | south => exact north5_south
   | east => exact north5_east
   | west => exact north5_west
   | northEast => exact north5_northEast
   | northWest => exact north5_northWest
   | southEast => exact north5_southEast
   | southWest => exact north5_southWest
 · exact north5_push
#print axioms north5
#print axioms north5_tags
end Owner1007.PreCage12
