/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks22
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block23 : List Dir := [.southWest, .northWest, .north, .east, .northEast, .south, .south, .south, .southWest, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east]
def soko3_2Macro147M764State764 : State := {player := 270, boulders := [113, 106, 112, 80], holes := []}
theorem soko3_2Macro147M764_block23_checked : run soko3_2.board soko3_2Macro147M764State736 soko3_2Macro147M764Block23 = some ⟨soko3_2Macro147M764State764, 11, 28⟩ := by decide +kernel
def soko3_2Macro147M764Prefix23 : List Dir := soko3_2Macro147M764Prefix22 ++ soko3_2Macro147M764Block23
theorem soko3_2Macro147M764_prefix23_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix23 = some ⟨soko3_2Macro147M764State764, 147, 764⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix22 soko3_2Macro147M764Block23
    ⟨soko3_2Macro147M764State736, 136, 736⟩ ⟨soko3_2Macro147M764State764, 11, 28⟩
    soko3_2Macro147M764_prefix22_checked soko3_2Macro147M764_block23_checked
end NetHack.Sokoban.Generated
