import Owner1007.Guard188One11Data
namespace Owner1007.Guard188One11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem walk3_north : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .north = true := by decide +kernel
theorem walk3_south : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .south = true := by decide +kernel
theorem walk3_east : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .east = true := by decide +kernel
theorem walk3_west : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .west = true := by decide +kernel
theorem walk3_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .northEast = true := by decide +kernel
theorem walk3_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .northWest = true := by decide +kernel
theorem walk3_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .southEast = true := by decide +kernel
theorem walk3_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .southWest = true := by decide +kernel
theorem pushes3 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨3,by decide⟩ = true := by decide +kernel
theorem node3 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨3,by decide⟩ = true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir
   · exact walk3_north
   · exact walk3_south
   · exact walk3_east
   · exact walk3_west
   · exact walk3_northEast
   · exact walk3_northWest
   · exact walk3_southEast
   · exact walk3_southWest
 · exact pushes3

end Owner1007.Guard188One11
