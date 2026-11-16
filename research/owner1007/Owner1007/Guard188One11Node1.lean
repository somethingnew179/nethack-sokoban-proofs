import Owner1007.Guard188One11Data
namespace Owner1007.Guard188One11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem walk1_north : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .north = true := by decide +kernel
theorem walk1_south : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .south = true := by decide +kernel
theorem walk1_east : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .east = true := by decide +kernel
theorem walk1_west : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .west = true := by decide +kernel
theorem walk1_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .northEast = true := by decide +kernel
theorem walk1_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .northWest = true := by decide +kernel
theorem walk1_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .southEast = true := by decide +kernel
theorem walk1_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .southWest = true := by decide +kernel
theorem pushes1 : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨1,by decide⟩ = true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨1,by decide⟩ = true := by
 apply FastCorral11.node_of_parts
 · intro dir
   cases dir
   · exact walk1_north
   · exact walk1_south
   · exact walk1_east
   · exact walk1_west
   · exact walk1_northEast
   · exact walk1_northWest
   · exact walk1_southEast
   · exact walk1_southWest
 · exact pushes1

end Owner1007.Guard188One11
