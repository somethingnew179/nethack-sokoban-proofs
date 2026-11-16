import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase18_north : FastCorral11.walkPart soko1_1.board locks region ⟨18,by decide⟩ .north = true := by decide +kernel
theorem phase18_south : FastCorral11.walkPart soko1_1.board locks region ⟨18,by decide⟩ .south = true := by decide +kernel
theorem phase18_east : FastCorral11.walkPart soko1_1.board locks region ⟨18,by decide⟩ .east = true := by decide +kernel
theorem phase18_west : FastCorral11.walkPart soko1_1.board locks region ⟨18,by decide⟩ .west = true := by decide +kernel
theorem phase18_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨18,by decide⟩ .northEast = true := by decide +kernel
theorem phase18_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨18,by decide⟩ .northWest = true := by decide +kernel
theorem phase18_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨18,by decide⟩ .southEast = true := by decide +kernel
theorem phase18_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨18,by decide⟩ .southWest = true := by decide +kernel
theorem phase18_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨18,by decide⟩ = true := by decide +kernel
theorem node18 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨18,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase18_north
    | south => exact phase18_south
    | east => exact phase18_east
    | west => exact phase18_west
    | northEast => exact phase18_northEast
    | northWest => exact phase18_northWest
    | southEast => exact phase18_southEast
    | southWest => exact phase18_southWest
  · exact phase18_pushes
#print axioms node18
end Owner1007.UpperZero11
