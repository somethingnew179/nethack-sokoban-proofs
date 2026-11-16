import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem ring3_north : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 3 .north=true := by decide +kernel
theorem ring3_south : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 3 .south=true := by decide +kernel
theorem ring3_east : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 3 .east=true := by decide +kernel
theorem ring3_west : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 3 .west=true := by decide +kernel
theorem ring3_northEast : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 3 .northEast=true := by decide +kernel
theorem ring3_northWest : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 3 .northWest=true := by decide +kernel
theorem ring3_southEast : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 3 .southEast=true := by decide +kernel
theorem ring3_southWest : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 3 .southWest=true := by decide +kernel
theorem ring3_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid 3=true := by decide +kernel
theorem ring3_tags : tagPart ringLocks ringRegion ringPaid ringAllowed 3=true := by decide +kernel
theorem ring3 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid 3=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact ring3_north
   | south => exact ring3_south
   | east => exact ring3_east
   | west => exact ring3_west
   | northEast => exact ring3_northEast
   | northWest => exact ring3_northWest
   | southEast => exact ring3_southEast
   | southWest => exact ring3_southWest
 · exact ring3_push
#print axioms ring3
#print axioms ring3_tags
end Owner1007.PreCage12
