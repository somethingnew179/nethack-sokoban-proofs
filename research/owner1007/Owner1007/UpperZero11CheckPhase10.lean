import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase10_north : FastCorral11.walkPart soko1_1.board locks region ⟨10,by decide⟩ .north = true := by decide +kernel
theorem phase10_south : FastCorral11.walkPart soko1_1.board locks region ⟨10,by decide⟩ .south = true := by decide +kernel
theorem phase10_east : FastCorral11.walkPart soko1_1.board locks region ⟨10,by decide⟩ .east = true := by decide +kernel
theorem phase10_west : FastCorral11.walkPart soko1_1.board locks region ⟨10,by decide⟩ .west = true := by decide +kernel
theorem phase10_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨10,by decide⟩ .northEast = true := by decide +kernel
theorem phase10_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨10,by decide⟩ .northWest = true := by decide +kernel
theorem phase10_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨10,by decide⟩ .southEast = true := by decide +kernel
theorem phase10_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨10,by decide⟩ .southWest = true := by decide +kernel
theorem phase10_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨10,by decide⟩ = true := by decide +kernel
theorem node10 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨10,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase10_north
    | south => exact phase10_south
    | east => exact phase10_east
    | west => exact phase10_west
    | northEast => exact phase10_northEast
    | northWest => exact phase10_northWest
    | southEast => exact phase10_southEast
    | southWest => exact phase10_southWest
  · exact phase10_pushes
#print axioms node10
end Owner1007.UpperZero11
