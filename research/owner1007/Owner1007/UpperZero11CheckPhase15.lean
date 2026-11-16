import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase15_north : FastCorral11.walkPart soko1_1.board locks region ⟨15,by decide⟩ .north = true := by decide +kernel
theorem phase15_south : FastCorral11.walkPart soko1_1.board locks region ⟨15,by decide⟩ .south = true := by decide +kernel
theorem phase15_east : FastCorral11.walkPart soko1_1.board locks region ⟨15,by decide⟩ .east = true := by decide +kernel
theorem phase15_west : FastCorral11.walkPart soko1_1.board locks region ⟨15,by decide⟩ .west = true := by decide +kernel
theorem phase15_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨15,by decide⟩ .northEast = true := by decide +kernel
theorem phase15_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨15,by decide⟩ .northWest = true := by decide +kernel
theorem phase15_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨15,by decide⟩ .southEast = true := by decide +kernel
theorem phase15_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨15,by decide⟩ .southWest = true := by decide +kernel
theorem phase15_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨15,by decide⟩ = true := by decide +kernel
theorem node15 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨15,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase15_north
    | south => exact phase15_south
    | east => exact phase15_east
    | west => exact phase15_west
    | northEast => exact phase15_northEast
    | northWest => exact phase15_northWest
    | southEast => exact phase15_southEast
    | southWest => exact phase15_southWest
  · exact phase15_pushes
#print axioms node15
end Owner1007.UpperZero11
