import Owner1007.PostCuts11Data
namespace Owner1007.PostCuts11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entry_north : FastCorral11.walkPart soko1_1.board entryLocks entryRegion ⟨0,by decide⟩ .north = true := by decide +kernel
theorem entry_south : FastCorral11.walkPart soko1_1.board entryLocks entryRegion ⟨0,by decide⟩ .south = true := by decide +kernel
theorem entry_east : FastCorral11.walkPart soko1_1.board entryLocks entryRegion ⟨0,by decide⟩ .east = true := by decide +kernel
theorem entry_west : FastCorral11.walkPart soko1_1.board entryLocks entryRegion ⟨0,by decide⟩ .west = true := by decide +kernel
theorem entry_northEast : FastCorral11.walkPart soko1_1.board entryLocks entryRegion ⟨0,by decide⟩ .northEast = true := by decide +kernel
theorem entry_northWest : FastCorral11.walkPart soko1_1.board entryLocks entryRegion ⟨0,by decide⟩ .northWest = true := by decide +kernel
theorem entry_southEast : FastCorral11.walkPart soko1_1.board entryLocks entryRegion ⟨0,by decide⟩ .southEast = true := by decide +kernel
theorem entry_southWest : FastCorral11.walkPart soko1_1.board entryLocks entryRegion ⟨0,by decide⟩ .southWest = true := by decide +kernel
theorem entry_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes entryLocks entryRegion entryPaid ⟨0,by decide⟩ = true := by decide +kernel
theorem entry_checked : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes entryLocks entryRegion entryPaid ⟨0,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact entry_north
    | south => exact entry_south
    | east => exact entry_east
    | west => exact entry_west
    | northEast => exact entry_northEast
    | northWest => exact entry_northWest
    | southEast => exact entry_southEast
    | southWest => exact entry_southWest
  · exact entry_pushes
#print axioms entry_checked
end Owner1007.PostCuts11
