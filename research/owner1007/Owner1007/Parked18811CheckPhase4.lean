import Owner1007.Parked18811Data
namespace Owner1007.Parked18811
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase4_north : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .north = true := by decide +kernel
theorem phase4_south : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .south = true := by decide +kernel
theorem phase4_east : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .east = true := by decide +kernel
theorem phase4_west : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .west = true := by decide +kernel
theorem phase4_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .northEast = true := by decide +kernel
theorem phase4_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .northWest = true := by decide +kernel
theorem phase4_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .southEast = true := by decide +kernel
theorem phase4_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨4,by decide⟩ .southWest = true := by decide +kernel
theorem phase4_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨4,by decide⟩ = true := by decide +kernel
theorem node4 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨4,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase4_north
    | south => exact phase4_south
    | east => exact phase4_east
    | west => exact phase4_west
    | northEast => exact phase4_northEast
    | northWest => exact phase4_northWest
    | southEast => exact phase4_southEast
    | southWest => exact phase4_southWest
  · exact phase4_pushes
#print axioms node4
end Owner1007.Parked18811
