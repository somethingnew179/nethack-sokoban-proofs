import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase9_north : FastCorral11.walkPart soko1_1.board locks region ⟨9,by decide⟩ .north = true := by decide +kernel
theorem phase9_south : FastCorral11.walkPart soko1_1.board locks region ⟨9,by decide⟩ .south = true := by decide +kernel
theorem phase9_east : FastCorral11.walkPart soko1_1.board locks region ⟨9,by decide⟩ .east = true := by decide +kernel
theorem phase9_west : FastCorral11.walkPart soko1_1.board locks region ⟨9,by decide⟩ .west = true := by decide +kernel
theorem phase9_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨9,by decide⟩ .northEast = true := by decide +kernel
theorem phase9_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨9,by decide⟩ .northWest = true := by decide +kernel
theorem phase9_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨9,by decide⟩ .southEast = true := by decide +kernel
theorem phase9_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨9,by decide⟩ .southWest = true := by decide +kernel
theorem phase9_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨9,by decide⟩ = true := by decide +kernel
theorem node9 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨9,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase9_north
    | south => exact phase9_south
    | east => exact phase9_east
    | west => exact phase9_west
    | northEast => exact phase9_northEast
    | northWest => exact phase9_northWest
    | southEast => exact phase9_southEast
    | southWest => exact phase9_southWest
  · exact phase9_pushes
#print axioms node9
end Owner1007.UpperZero11
