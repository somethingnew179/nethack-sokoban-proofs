import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem ring0_north : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 0 .north=true := by decide +kernel
theorem ring0_south : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 0 .south=true := by decide +kernel
theorem ring0_east : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 0 .east=true := by decide +kernel
theorem ring0_west : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 0 .west=true := by decide +kernel
theorem ring0_northEast : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 0 .northEast=true := by decide +kernel
theorem ring0_northWest : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 0 .northWest=true := by decide +kernel
theorem ring0_southEast : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 0 .southEast=true := by decide +kernel
theorem ring0_southWest : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 0 .southWest=true := by decide +kernel
theorem ring0_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid 0=true := by decide +kernel
theorem ring0_tags : tagPart ringLocks ringRegion ringPaid ringAllowed 0=true := by decide +kernel
theorem ring0 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid 0=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact ring0_north
   | south => exact ring0_south
   | east => exact ring0_east
   | west => exact ring0_west
   | northEast => exact ring0_northEast
   | northWest => exact ring0_northWest
   | southEast => exact ring0_southEast
   | southWest => exact ring0_southWest
 · exact ring0_push
#print axioms ring0
#print axioms ring0_tags
end Owner1007.PreCage12
