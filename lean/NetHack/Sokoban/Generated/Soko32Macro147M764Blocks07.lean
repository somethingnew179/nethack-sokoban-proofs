/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks06
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block7 : List Dir := [.southWest, .southWest, .west, .west, .west, .west, .west, .northWest, .northWest, .north, .north, .northEast, .northEast, .east, .northEast, .east, .south, .south, .east, .northEast, .southEast, .southEast, .south, .southWest, .west, .west, .south, .northEast, .east, .northEast, .north, .northWest]
def soko3_2Macro147M764State256 : State := {player := 165, boulders := [293, 188, 214, 215, 270, 113, 266, 265, 135, 106, 159, 112, 80, 161], holes := [274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block7_checked : run soko3_2.board soko3_2Macro147M764State224 soko3_2Macro147M764Block7 = some ⟨soko3_2Macro147M764State256, 3, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix7 : List Dir := soko3_2Macro147M764Prefix6 ++ soko3_2Macro147M764Block7
theorem soko3_2Macro147M764_prefix7_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix7 = some ⟨soko3_2Macro147M764State256, 42, 256⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix6 soko3_2Macro147M764Block7
    ⟨soko3_2Macro147M764State224, 39, 224⟩ ⟨soko3_2Macro147M764State256, 3, 32⟩
    soko3_2Macro147M764_prefix6_checked soko3_2Macro147M764_block7_checked
end NetHack.Sokoban.Generated
