/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks15
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block16 : List Dir := [.south, .south, .southWest, .east, .west, .northWest, .west, .south, .northEast, .east, .northEast, .north, .northWest, .northWest, .southWest, .south, .south, .south, .northWest, .west, .west, .west, .west, .southWest, .southEast, .east, .southEast, .east, .east, .east, .east, .southEast]
def soko3_2Macro147M764State544 : State := {player := 321, boulders := [295, 267, 113, 266, 265, 106, 159, 112, 80, 161], holes := [278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block16_checked : run soko3_2.board soko3_2Macro147M764State512 soko3_2Macro147M764Block16 = some ⟨soko3_2Macro147M764State544, 7, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix16 : List Dir := soko3_2Macro147M764Prefix15 ++ soko3_2Macro147M764Block16
theorem soko3_2Macro147M764_prefix16_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix16 = some ⟨soko3_2Macro147M764State544, 85, 544⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix15 soko3_2Macro147M764Block16
    ⟨soko3_2Macro147M764State512, 78, 512⟩ ⟨soko3_2Macro147M764State544, 7, 32⟩
    soko3_2Macro147M764_prefix15_checked soko3_2Macro147M764_block16_checked
end NetHack.Sokoban.Generated
