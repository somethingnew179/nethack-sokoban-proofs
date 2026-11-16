import Owner1007.Guard188One11Data
namespace Owner1007.Guard188One11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem walk2_north : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .north = true := by decide +kernel
theorem walk2_south : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .south = true := by decide +kernel
theorem walk2_east : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .east = true := by decide +kernel
theorem walk2_west : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .west = true := by decide +kernel
theorem walk2_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .northEast = true := by decide +kernel
theorem walk2_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .northWest = true := by decide +kernel
theorem walk2_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .southEast = true := by decide +kernel
theorem walk2_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .southWest = true := by decide +kernel
theorem pushes2 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨2,by decide⟩ = true := by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨2,by decide⟩ = true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir
   · exact walk2_north
   · exact walk2_south
   · exact walk2_east
   · exact walk2_west
   · exact walk2_northEast
   · exact walk2_northWest
   · exact walk2_southEast
   · exact walk2_southWest
 · exact pushes2

end Owner1007.Guard188One11
