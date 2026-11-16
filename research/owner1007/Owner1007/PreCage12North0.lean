import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north0_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 0 .north=true := by decide +kernel
theorem north0_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 0 .south=true := by decide +kernel
theorem north0_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 0 .east=true := by decide +kernel
theorem north0_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 0 .west=true := by decide +kernel
theorem north0_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 0 .northEast=true := by decide +kernel
theorem north0_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 0 .northWest=true := by decide +kernel
theorem north0_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 0 .southEast=true := by decide +kernel
theorem north0_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 0 .southWest=true := by decide +kernel
theorem north0_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 0=true := by decide +kernel
theorem north0_tags : tagPart northLocks northRegion northPaid northAllowed 0=true := by decide +kernel
theorem north0 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 0=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north0_north
   | south => exact north0_south
   | east => exact north0_east
   | west => exact north0_west
   | northEast => exact north0_northEast
   | northWest => exact north0_northWest
   | southEast => exact north0_southEast
   | southWest => exact north0_southWest
 · exact north0_push
#print axioms north0
#print axioms north0_tags
end Owner1007.PreCage12
