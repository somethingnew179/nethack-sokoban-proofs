import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase1_north : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .north = true := by decide +kernel
theorem phase1_south : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .south = true := by decide +kernel
theorem phase1_east : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .east = true := by decide +kernel
theorem phase1_west : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .west = true := by decide +kernel
theorem phase1_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .northEast = true := by decide +kernel
theorem phase1_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .northWest = true := by decide +kernel
theorem phase1_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .southEast = true := by decide +kernel
theorem phase1_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨1,by decide⟩ .southWest = true := by decide +kernel
theorem phase1_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨1,by decide⟩ = true := by decide +kernel
theorem node1 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨1,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase1_north
    | south => exact phase1_south
    | east => exact phase1_east
    | west => exact phase1_west
    | northEast => exact phase1_northEast
    | northWest => exact phase1_northWest
    | southEast => exact phase1_southEast
    | southWest => exact phase1_southWest
  · exact phase1_pushes
#print axioms node1
end Owner1007.UpperZero11
