import Owner1007.LeftPair11Data
namespace Owner1007.LeftPair11
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem first_north : FastCorral11.walkPart soko1_1.board cut0Locks cut0Region ⟨0,by decide⟩ .north = true := by decide +kernel
theorem first_south : FastCorral11.walkPart soko1_1.board cut0Locks cut0Region ⟨0,by decide⟩ .south = true := by decide +kernel
theorem first_east : FastCorral11.walkPart soko1_1.board cut0Locks cut0Region ⟨0,by decide⟩ .east = true := by decide +kernel
theorem first_west : FastCorral11.walkPart soko1_1.board cut0Locks cut0Region ⟨0,by decide⟩ .west = true := by decide +kernel
theorem first_northEast : FastCorral11.walkPart soko1_1.board cut0Locks cut0Region ⟨0,by decide⟩ .northEast = true := by decide +kernel
theorem first_northWest : FastCorral11.walkPart soko1_1.board cut0Locks cut0Region ⟨0,by decide⟩ .northWest = true := by decide +kernel
theorem first_southEast : FastCorral11.walkPart soko1_1.board cut0Locks cut0Region ⟨0,by decide⟩ .southEast = true := by decide +kernel
theorem first_southWest : FastCorral11.walkPart soko1_1.board cut0Locks cut0Region ⟨0,by decide⟩ .southWest = true := by decide +kernel
theorem first_pushes : FastCorral11.pushPart soko1_1.board soko1_1.initial.holes cut0Locks cut0Region cut0Paid ⟨0,by decide⟩ = true := by decide +kernel
theorem first_checked : FastCorral11.nodeCheck soko1_1.board soko1_1.initial.holes cut0Locks cut0Region cut0Paid ⟨0,by decide⟩ = true := by
  apply FastCorral11.node_of_parts
  · intro dir
    cases dir with
    | north => exact first_north
    | south => exact first_south
    | east => exact first_east
    | west => exact first_west
    | northEast => exact first_northEast
    | northWest => exact first_northWest
    | southEast => exact first_southEast
    | southWest => exact first_southWest
  · exact first_pushes
#print axioms first_checked
end Owner1007.LeftPair11
