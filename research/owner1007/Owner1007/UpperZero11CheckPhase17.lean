import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase17_north : FastCorral11.walkPart soko1_1.board locks region ⟨17,by decide⟩ .north = true := by decide +kernel
theorem phase17_south : FastCorral11.walkPart soko1_1.board locks region ⟨17,by decide⟩ .south = true := by decide +kernel
theorem phase17_east : FastCorral11.walkPart soko1_1.board locks region ⟨17,by decide⟩ .east = true := by decide +kernel
theorem phase17_west : FastCorral11.walkPart soko1_1.board locks region ⟨17,by decide⟩ .west = true := by decide +kernel
theorem phase17_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨17,by decide⟩ .northEast = true := by decide +kernel
theorem phase17_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨17,by decide⟩ .northWest = true := by decide +kernel
theorem phase17_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨17,by decide⟩ .southEast = true := by decide +kernel
theorem phase17_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨17,by decide⟩ .southWest = true := by decide +kernel
theorem phase17_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨17,by decide⟩ = true := by decide +kernel
theorem node17 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨17,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase17_north
    | south => exact phase17_south
    | east => exact phase17_east
    | west => exact phase17_west
    | northEast => exact phase17_northEast
    | northWest => exact phase17_northWest
    | southEast => exact phase17_southEast
    | southWest => exact phase17_southWest
  · exact phase17_pushes
#print axioms node17
end Owner1007.UpperZero11
