import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase14_north : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .north = true := by decide +kernel
theorem phase14_south : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .south = true := by decide +kernel
theorem phase14_east : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .east = true := by decide +kernel
theorem phase14_west : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .west = true := by decide +kernel
theorem phase14_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .northEast = true := by decide +kernel
theorem phase14_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .northWest = true := by decide +kernel
theorem phase14_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .southEast = true := by decide +kernel
theorem phase14_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨14,by decide⟩ .southWest = true := by decide +kernel
theorem phase14_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨14,by decide⟩ = true := by decide +kernel
theorem node14 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨14,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase14_north
    | south => exact phase14_south
    | east => exact phase14_east
    | west => exact phase14_west
    | northEast => exact phase14_northEast
    | northWest => exact phase14_northWest
    | southEast => exact phase14_southEast
    | southWest => exact phase14_southWest
  · exact phase14_pushes
#print axioms node14
end Owner1007.UpperZero11
