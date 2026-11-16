import Owner1007.Guard188One11Data
namespace Owner1007.Guard188One11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem walk0_north : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .north = true := by decide +kernel
theorem walk0_south : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .south = true := by decide +kernel
theorem walk0_east : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .east = true := by decide +kernel
theorem walk0_west : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .west = true := by decide +kernel
theorem walk0_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northEast = true := by decide +kernel
theorem walk0_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northWest = true := by decide +kernel
theorem walk0_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southEast = true := by decide +kernel
theorem walk0_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southWest = true := by decide +kernel
theorem pushes0 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩ = true := by decide +kernel
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩ = true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir
   · exact walk0_north
   · exact walk0_south
   · exact walk0_east
   · exact walk0_west
   · exact walk0_northEast
   · exact walk0_northWest
   · exact walk0_southEast
   · exact walk0_southWest
 · exact pushes0

end Owner1007.Guard188One11
