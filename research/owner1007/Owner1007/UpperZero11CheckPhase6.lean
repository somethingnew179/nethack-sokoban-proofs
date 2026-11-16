import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase6_north : FastCorral11.walkPart soko1_1.board locks region ⟨6,by decide⟩ .north = true := by decide +kernel
theorem phase6_south : FastCorral11.walkPart soko1_1.board locks region ⟨6,by decide⟩ .south = true := by decide +kernel
theorem phase6_east : FastCorral11.walkPart soko1_1.board locks region ⟨6,by decide⟩ .east = true := by decide +kernel
theorem phase6_west : FastCorral11.walkPart soko1_1.board locks region ⟨6,by decide⟩ .west = true := by decide +kernel
theorem phase6_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨6,by decide⟩ .northEast = true := by decide +kernel
theorem phase6_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨6,by decide⟩ .northWest = true := by decide +kernel
theorem phase6_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨6,by decide⟩ .southEast = true := by decide +kernel
theorem phase6_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨6,by decide⟩ .southWest = true := by decide +kernel
theorem phase6_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨6,by decide⟩ = true := by decide +kernel
theorem node6 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨6,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase6_north
    | south => exact phase6_south
    | east => exact phase6_east
    | west => exact phase6_west
    | northEast => exact phase6_northEast
    | northWest => exact phase6_northWest
    | southEast => exact phase6_southEast
    | southWest => exact phase6_southWest
  · exact phase6_pushes
#print axioms node6
end Owner1007.UpperZero11
