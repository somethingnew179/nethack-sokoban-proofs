import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem ring2_north : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 2 .north=true := by decide +kernel
theorem ring2_south : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 2 .south=true := by decide +kernel
theorem ring2_east : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 2 .east=true := by decide +kernel
theorem ring2_west : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 2 .west=true := by decide +kernel
theorem ring2_northEast : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 2 .northEast=true := by decide +kernel
theorem ring2_northWest : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 2 .northWest=true := by decide +kernel
theorem ring2_southEast : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 2 .southEast=true := by decide +kernel
theorem ring2_southWest : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 2 .southWest=true := by decide +kernel
theorem ring2_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid 2=true := by decide +kernel
theorem ring2_tags : tagPart ringLocks ringRegion ringPaid ringAllowed 2=true := by decide +kernel
theorem ring2 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid 2=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact ring2_north
   | south => exact ring2_south
   | east => exact ring2_east
   | west => exact ring2_west
   | northEast => exact ring2_northEast
   | northWest => exact ring2_northWest
   | southEast => exact ring2_southEast
   | southWest => exact ring2_southWest
 · exact ring2_push
#print axioms ring2
#print axioms ring2_tags
end Owner1007.PreCage12
