import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem north4_north : FastCorral11.walkPart soko1_2.board northLocks northRegion 4 .north=true := by decide +kernel
theorem north4_south : FastCorral11.walkPart soko1_2.board northLocks northRegion 4 .south=true := by decide +kernel
theorem north4_east : FastCorral11.walkPart soko1_2.board northLocks northRegion 4 .east=true := by decide +kernel
theorem north4_west : FastCorral11.walkPart soko1_2.board northLocks northRegion 4 .west=true := by decide +kernel
theorem north4_northEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 4 .northEast=true := by decide +kernel
theorem north4_northWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 4 .northWest=true := by decide +kernel
theorem north4_southEast : FastCorral11.walkPart soko1_2.board northLocks northRegion 4 .southEast=true := by decide +kernel
theorem north4_southWest : FastCorral11.walkPart soko1_2.board northLocks northRegion 4 .southWest=true := by decide +kernel
theorem north4_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 4=true := by decide +kernel
theorem north4_tags : tagPart northLocks northRegion northPaid northAllowed 4=true := by decide +kernel
theorem north4 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes northLocks northRegion northPaid 4=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact north4_north
   | south => exact north4_south
   | east => exact north4_east
   | west => exact north4_west
   | northEast => exact north4_northEast
   | northWest => exact north4_northWest
   | southEast => exact north4_southEast
   | southWest => exact north4_southWest
 · exact north4_push
#print axioms north4
#print axioms north4_tags
end Owner1007.PreCage12
