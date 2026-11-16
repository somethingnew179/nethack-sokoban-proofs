import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase7_north : FastCorral11.walkPart soko1_1.board locks region ⟨7,by decide⟩ .north = true := by decide +kernel
theorem phase7_south : FastCorral11.walkPart soko1_1.board locks region ⟨7,by decide⟩ .south = true := by decide +kernel
theorem phase7_east : FastCorral11.walkPart soko1_1.board locks region ⟨7,by decide⟩ .east = true := by decide +kernel
theorem phase7_west : FastCorral11.walkPart soko1_1.board locks region ⟨7,by decide⟩ .west = true := by decide +kernel
theorem phase7_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨7,by decide⟩ .northEast = true := by decide +kernel
theorem phase7_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨7,by decide⟩ .northWest = true := by decide +kernel
theorem phase7_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨7,by decide⟩ .southEast = true := by decide +kernel
theorem phase7_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨7,by decide⟩ .southWest = true := by decide +kernel
theorem phase7_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨7,by decide⟩ = true := by decide +kernel
theorem node7 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨7,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase7_north
    | south => exact phase7_south
    | east => exact phase7_east
    | west => exact phase7_west
    | northEast => exact phase7_northEast
    | northWest => exact phase7_northWest
    | southEast => exact phase7_southEast
    | southWest => exact phase7_southWest
  · exact phase7_pushes
#print axioms node7
end Owner1007.UpperZero11
