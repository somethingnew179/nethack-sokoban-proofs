import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase16_north : FastCorral11.walkPart soko1_1.board locks region ⟨16,by decide⟩ .north = true := by decide +kernel
theorem phase16_south : FastCorral11.walkPart soko1_1.board locks region ⟨16,by decide⟩ .south = true := by decide +kernel
theorem phase16_east : FastCorral11.walkPart soko1_1.board locks region ⟨16,by decide⟩ .east = true := by decide +kernel
theorem phase16_west : FastCorral11.walkPart soko1_1.board locks region ⟨16,by decide⟩ .west = true := by decide +kernel
theorem phase16_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨16,by decide⟩ .northEast = true := by decide +kernel
theorem phase16_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨16,by decide⟩ .northWest = true := by decide +kernel
theorem phase16_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨16,by decide⟩ .southEast = true := by decide +kernel
theorem phase16_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨16,by decide⟩ .southWest = true := by decide +kernel
theorem phase16_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨16,by decide⟩ = true := by decide +kernel
theorem node16 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨16,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase16_north
    | south => exact phase16_south
    | east => exact phase16_east
    | west => exact phase16_west
    | northEast => exact phase16_northEast
    | northWest => exact phase16_northWest
    | southEast => exact phase16_southEast
    | southWest => exact phase16_southWest
  · exact phase16_pushes
#print axioms node16
end Owner1007.UpperZero11
