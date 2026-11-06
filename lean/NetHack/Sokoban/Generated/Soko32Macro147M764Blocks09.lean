/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks08
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block9 : List Dir := [.north, .northWest, .northWest, .southWest, .south, .south, .south, .east, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .southWest, .west, .west, .west, .west, .west, .northWest, .northWest, .northEast, .east, .east, .east, .east, .west]
def soko3_2Macro147M764State320 : State := {player := 213, boulders := [215, 270, 267, 136, 188, 113, 266, 265, 106, 159, 112, 80, 161], holes := [275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block9_checked : run soko3_2.board soko3_2Macro147M764State288 soko3_2Macro147M764Block9 = some ⟨soko3_2Macro147M764State320, 5, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix9 : List Dir := soko3_2Macro147M764Prefix8 ++ soko3_2Macro147M764Block9
theorem soko3_2Macro147M764_prefix9_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix9 = some ⟨soko3_2Macro147M764State320, 53, 320⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix8 soko3_2Macro147M764Block9
    ⟨soko3_2Macro147M764State288, 48, 288⟩ ⟨soko3_2Macro147M764State320, 5, 32⟩
    soko3_2Macro147M764_prefix8_checked soko3_2Macro147M764_block9_checked
end NetHack.Sokoban.Generated
