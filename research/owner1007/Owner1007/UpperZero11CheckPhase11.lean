import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase11_north : FastCorral11.walkPart soko1_1.board locks region ⟨11,by decide⟩ .north = true := by decide +kernel
theorem phase11_south : FastCorral11.walkPart soko1_1.board locks region ⟨11,by decide⟩ .south = true := by decide +kernel
theorem phase11_east : FastCorral11.walkPart soko1_1.board locks region ⟨11,by decide⟩ .east = true := by decide +kernel
theorem phase11_west : FastCorral11.walkPart soko1_1.board locks region ⟨11,by decide⟩ .west = true := by decide +kernel
theorem phase11_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨11,by decide⟩ .northEast = true := by decide +kernel
theorem phase11_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨11,by decide⟩ .northWest = true := by decide +kernel
theorem phase11_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨11,by decide⟩ .southEast = true := by decide +kernel
theorem phase11_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨11,by decide⟩ .southWest = true := by decide +kernel
theorem phase11_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨11,by decide⟩ = true := by decide +kernel
theorem node11 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨11,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase11_north
    | south => exact phase11_south
    | east => exact phase11_east
    | west => exact phase11_west
    | northEast => exact phase11_northEast
    | northWest => exact phase11_northWest
    | southEast => exact phase11_southEast
    | southWest => exact phase11_southWest
  · exact phase11_pushes
#print axioms node11
end Owner1007.UpperZero11
