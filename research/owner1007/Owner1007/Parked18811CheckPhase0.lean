import Owner1007.Parked18811Data
namespace Owner1007.Parked18811
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase0_north : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .north = true := by decide +kernel
theorem phase0_south : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .south = true := by decide +kernel
theorem phase0_east : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .east = true := by decide +kernel
theorem phase0_west : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .west = true := by decide +kernel
theorem phase0_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northEast = true := by decide +kernel
theorem phase0_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .northWest = true := by decide +kernel
theorem phase0_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southEast = true := by decide +kernel
theorem phase0_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨0,by decide⟩ .southWest = true := by decide +kernel
theorem phase0_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩ = true := by decide +kernel
theorem node0 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨0,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase0_north
    | south => exact phase0_south
    | east => exact phase0_east
    | west => exact phase0_west
    | northEast => exact phase0_northEast
    | northWest => exact phase0_northWest
    | southEast => exact phase0_southEast
    | southWest => exact phase0_southWest
  · exact phase0_pushes
#print axioms node0
end Owner1007.Parked18811
