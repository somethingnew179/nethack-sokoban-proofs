import Owner1007.PostCuts11Data
namespace Owner1007.PostCuts11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem right_north : FastCorral11.walkPart soko1_1.board rightLocks rightRegion ⟨0,by decide⟩ .north = true := by decide +kernel
theorem right_south : FastCorral11.walkPart soko1_1.board rightLocks rightRegion ⟨0,by decide⟩ .south = true := by decide +kernel
theorem right_east : FastCorral11.walkPart soko1_1.board rightLocks rightRegion ⟨0,by decide⟩ .east = true := by decide +kernel
theorem right_west : FastCorral11.walkPart soko1_1.board rightLocks rightRegion ⟨0,by decide⟩ .west = true := by decide +kernel
theorem right_northEast : FastCorral11.walkPart soko1_1.board rightLocks rightRegion ⟨0,by decide⟩ .northEast = true := by decide +kernel
theorem right_northWest : FastCorral11.walkPart soko1_1.board rightLocks rightRegion ⟨0,by decide⟩ .northWest = true := by decide +kernel
theorem right_southEast : FastCorral11.walkPart soko1_1.board rightLocks rightRegion ⟨0,by decide⟩ .southEast = true := by decide +kernel
theorem right_southWest : FastCorral11.walkPart soko1_1.board rightLocks rightRegion ⟨0,by decide⟩ .southWest = true := by decide +kernel
theorem right_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes rightLocks rightRegion rightPaid ⟨0,by decide⟩ = true := by decide +kernel
theorem right_checked : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes rightLocks rightRegion rightPaid ⟨0,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact right_north
    | south => exact right_south
    | east => exact right_east
    | west => exact right_west
    | northEast => exact right_northEast
    | northWest => exact right_northWest
    | southEast => exact right_southEast
    | southWest => exact right_southWest
  · exact right_pushes
#print axioms right_checked
end Owner1007.PostCuts11
