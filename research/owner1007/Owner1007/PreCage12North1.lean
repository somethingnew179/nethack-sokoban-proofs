import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north1_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 1 .north=true := by decide +kernel
theorem north1_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 1 .south=true := by decide +kernel
theorem north1_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 1 .east=true := by decide +kernel
theorem north1_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 1 .west=true := by decide +kernel
theorem north1_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 1 .northEast=true := by decide +kernel
theorem north1_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 1 .northWest=true := by decide +kernel
theorem north1_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 1 .southEast=true := by decide +kernel
theorem north1_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 1 .southWest=true := by decide +kernel
theorem north1_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 1=true := by decide +kernel
theorem north1_tags : tagPart northLocks northRegion northPaid northAllowed 1=true := by decide +kernel
theorem north1 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 1=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north1_north
   | south => exact north1_south
   | east => exact north1_east
   | west => exact north1_west
   | northEast => exact north1_northEast
   | northWest => exact north1_northWest
   | southEast => exact north1_southEast
   | southWest => exact north1_southWest
 · exact north1_push
#print axioms north1
#print axioms north1_tags
end Owner1007.PreCage12
