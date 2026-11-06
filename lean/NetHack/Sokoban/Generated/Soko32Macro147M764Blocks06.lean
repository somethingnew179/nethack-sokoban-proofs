/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks05
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block6 : List Dir := [.northEast, .east, .east, .east, .east, .west, .west, .west, .west, .southWest, .southEast, .east, .southEast, .east, .east, .east, .east, .northEast, .north, .northEast, .north, .northWest, .northWest, .west, .southWest, .south, .northEast, .northEast, .southEast, .southEast, .south, .south]
def soko3_2Macro147M764State224 : State := {player := 244, boulders := [214, 215, 270, 267, 136, 113, 266, 265, 135, 106, 159, 112, 80, 161], holes := [274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block6_checked : run soko3_2.board soko3_2Macro147M764State192 soko3_2Macro147M764Block6 = some ⟨soko3_2Macro147M764State224, 2, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix6 : List Dir := soko3_2Macro147M764Prefix5 ++ soko3_2Macro147M764Block6
theorem soko3_2Macro147M764_prefix6_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix6 = some ⟨soko3_2Macro147M764State224, 39, 224⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix5 soko3_2Macro147M764Block6
    ⟨soko3_2Macro147M764State192, 37, 192⟩ ⟨soko3_2Macro147M764State224, 2, 32⟩
    soko3_2Macro147M764_prefix5_checked soko3_2Macro147M764_block6_checked
end NetHack.Sokoban.Generated
