import Owner1007.PreCage12Data
namespace Owner1007.PreCage12
open NetHack.Sokoban
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem ring1_north : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 1 .north=true := by decide +kernel
theorem ring1_south : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 1 .south=true := by decide +kernel
theorem ring1_east : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 1 .east=true := by decide +kernel
theorem ring1_west : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 1 .west=true := by decide +kernel
theorem ring1_northEast : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 1 .northEast=true := by decide +kernel
theorem ring1_northWest : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 1 .northWest=true := by decide +kernel
theorem ring1_southEast : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 1 .southEast=true := by decide +kernel
theorem ring1_southWest : FastCorral11.walkPart soko1_2.board ringLocks ringRegion 1 .southWest=true := by decide +kernel
theorem ring1_push : FastCorral11.pushPart soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid 1=true := by decide +kernel
theorem ring1_tags : tagPart ringLocks ringRegion ringPaid ringAllowed 1=true := by decide +kernel
theorem ring1 : FastCorral11.nodeCheck soko1_2.board soko1_2.initial.holes ringLocks ringRegion ringPaid 1=true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir with
   | north => exact ring1_north
   | south => exact ring1_south
   | east => exact ring1_east
   | west => exact ring1_west
   | northEast => exact ring1_northEast
   | northWest => exact ring1_northWest
   | southEast => exact ring1_southEast
   | southWest => exact ring1_southWest
 · exact ring1_push
#print axioms ring1
#print axioms ring1_tags
end Owner1007.PreCage12
