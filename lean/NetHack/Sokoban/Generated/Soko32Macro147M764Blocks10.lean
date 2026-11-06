/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks09
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block10 : List Dir := [.west, .west, .west, .southWest, .southEast, .east, .southEast, .east, .east, .east, .east, .northEast, .north, .northEast, .north, .northWest, .northWest, .west, .southWest, .south, .northEast, .northEast, .southEast, .southEast, .south, .south, .southWest, .southWest, .west, .west, .west, .west]
def soko3_2Macro147M764State352 : State := {player := 290, boulders := [214, 215, 270, 267, 136, 113, 266, 265, 106, 159, 112, 80, 161], holes := [275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block10_checked : run soko3_2.board soko3_2Macro147M764State320 soko3_2Macro147M764Block10 = some ⟨soko3_2Macro147M764State352, 1, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix10 : List Dir := soko3_2Macro147M764Prefix9 ++ soko3_2Macro147M764Block10
theorem soko3_2Macro147M764_prefix10_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix10 = some ⟨soko3_2Macro147M764State352, 54, 352⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix9 soko3_2Macro147M764Block10
    ⟨soko3_2Macro147M764State320, 53, 320⟩ ⟨soko3_2Macro147M764State352, 1, 32⟩
    soko3_2Macro147M764_prefix9_checked soko3_2Macro147M764_block10_checked
end NetHack.Sokoban.Generated
