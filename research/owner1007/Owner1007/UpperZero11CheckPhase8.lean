import Owner1007.UpperZero11Data
namespace Owner1007.UpperZero11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase8_north : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .north = true := by decide +kernel
theorem phase8_south : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .south = true := by decide +kernel
theorem phase8_east : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .east = true := by decide +kernel
theorem phase8_west : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .west = true := by decide +kernel
theorem phase8_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .northEast = true := by decide +kernel
theorem phase8_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .northWest = true := by decide +kernel
theorem phase8_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .southEast = true := by decide +kernel
theorem phase8_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨8,by decide⟩ .southWest = true := by decide +kernel
theorem phase8_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨8,by decide⟩ = true := by decide +kernel
theorem node8 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨8,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase8_north
    | south => exact phase8_south
    | east => exact phase8_east
    | west => exact phase8_west
    | northEast => exact phase8_northEast
    | northWest => exact phase8_northWest
    | southEast => exact phase8_southEast
    | southWest => exact phase8_southWest
  · exact phase8_pushes
#print axioms node8
end Owner1007.UpperZero11
