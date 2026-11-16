import Owner1007.Parked18811Data
namespace Owner1007.Parked18811
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase2_north : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .north = true := by decide +kernel
theorem phase2_south : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .south = true := by decide +kernel
theorem phase2_east : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .east = true := by decide +kernel
theorem phase2_west : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .west = true := by decide +kernel
theorem phase2_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .northEast = true := by decide +kernel
theorem phase2_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .northWest = true := by decide +kernel
theorem phase2_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .southEast = true := by decide +kernel
theorem phase2_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨2,by decide⟩ .southWest = true := by decide +kernel
theorem phase2_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨2,by decide⟩ = true := by decide +kernel
theorem node2 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨2,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase2_north
    | south => exact phase2_south
    | east => exact phase2_east
    | west => exact phase2_west
    | northEast => exact phase2_northEast
    | northWest => exact phase2_northWest
    | southEast => exact phase2_southEast
    | southWest => exact phase2_southWest
  · exact phase2_pushes
#print axioms node2
end Owner1007.Parked18811
