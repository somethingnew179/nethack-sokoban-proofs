import Owner1007.Parked18811Data
namespace Owner1007.Parked18811
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase5_north : FastCorral11.walkPart soko1_1.board locks region ⟨5,by decide⟩ .north = true := by decide +kernel
theorem phase5_south : FastCorral11.walkPart soko1_1.board locks region ⟨5,by decide⟩ .south = true := by decide +kernel
theorem phase5_east : FastCorral11.walkPart soko1_1.board locks region ⟨5,by decide⟩ .east = true := by decide +kernel
theorem phase5_west : FastCorral11.walkPart soko1_1.board locks region ⟨5,by decide⟩ .west = true := by decide +kernel
theorem phase5_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨5,by decide⟩ .northEast = true := by decide +kernel
theorem phase5_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨5,by decide⟩ .northWest = true := by decide +kernel
theorem phase5_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨5,by decide⟩ .southEast = true := by decide +kernel
theorem phase5_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨5,by decide⟩ .southWest = true := by decide +kernel
theorem phase5_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨5,by decide⟩ = true := by decide +kernel
theorem node5 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨5,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase5_north
    | south => exact phase5_south
    | east => exact phase5_east
    | west => exact phase5_west
    | northEast => exact phase5_northEast
    | northWest => exact phase5_northWest
    | southEast => exact phase5_southEast
    | southWest => exact phase5_southWest
  · exact phase5_pushes
#print axioms node5
end Owner1007.Parked18811
