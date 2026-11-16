import Owner1007.Guard188One11Data
namespace Owner1007.Guard188One11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem walk4_north : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .north = true := by decide +kernel
theorem walk4_south : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .south = true := by decide +kernel
theorem walk4_east : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .east = true := by decide +kernel
theorem walk4_west : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .west = true := by decide +kernel
theorem walk4_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .northEast = true := by decide +kernel
theorem walk4_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .northWest = true := by decide +kernel
theorem walk4_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .southEast = true := by decide +kernel
theorem walk4_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .southWest = true := by decide +kernel
theorem pushes4 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨4,by decide⟩ = true := by decide +kernel
theorem node4 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨4,by decide⟩ = true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir
   · exact walk4_north
   · exact walk4_south
   · exact walk4_east
   · exact walk4_west
   · exact walk4_northEast
   · exact walk4_northWest
   · exact walk4_southEast
   · exact walk4_southWest
 · exact pushes4

end Owner1007.Guard188One11
