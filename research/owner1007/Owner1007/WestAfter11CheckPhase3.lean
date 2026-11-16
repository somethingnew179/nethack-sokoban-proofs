import Owner1007.WestAfter11Data
namespace Owner1007.WestAfter11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem phase3_north : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .north = true := by decide +kernel
theorem phase3_south : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .south = true := by decide +kernel
theorem phase3_east : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .east = true := by decide +kernel
theorem phase3_west : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .west = true := by decide +kernel
theorem phase3_northEast : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .northEast = true := by decide +kernel
theorem phase3_northWest : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .northWest = true := by decide +kernel
theorem phase3_southEast : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .southEast = true := by decide +kernel
theorem phase3_southWest : FastCorral11.walkPart soko1_1.board locks region ⟨3,by decide⟩ .southWest = true := by decide +kernel
theorem phase3_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes locks region paid ⟨3,by decide⟩ = true := by decide +kernel
theorem node3 : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes locks region paid ⟨3,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact phase3_north
    | south => exact phase3_south
    | east => exact phase3_east
    | west => exact phase3_west
    | northEast => exact phase3_northEast
    | northWest => exact phase3_northWest
    | southEast => exact phase3_southEast
    | southWest => exact phase3_southWest
  · exact phase3_pushes
#print axioms node3
end Owner1007.WestAfter11
