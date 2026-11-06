/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks04
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block5 : List Dir := [.east, .southEast, .north, .north, .northEast, .north, .north, .northWest, .northWest, .southWest, .south, .south, .south, .east, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .southWest, .west, .west, .west, .west, .west, .northWest, .northWest]
def soko3_2Macro147M764State192 : State := {player := 235, boulders := [270, 267, 136, 113, 266, 265, 214, 135, 106, 159, 112, 80, 161, 188], holes := [274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block5_checked : run soko3_2.board soko3_2Macro147M764State160 soko3_2Macro147M764Block5 = some ⟨soko3_2Macro147M764State192, 6, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix5 : List Dir := soko3_2Macro147M764Prefix4 ++ soko3_2Macro147M764Block5
theorem soko3_2Macro147M764_prefix5_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix5 = some ⟨soko3_2Macro147M764State192, 37, 192⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix4 soko3_2Macro147M764Block5
    ⟨soko3_2Macro147M764State160, 31, 160⟩ ⟨soko3_2Macro147M764State192, 6, 32⟩
    soko3_2Macro147M764_prefix4_checked soko3_2Macro147M764_block5_checked
end NetHack.Sokoban.Generated
