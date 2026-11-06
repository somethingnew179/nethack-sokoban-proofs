/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks07
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block8 : List Dir := [.northWest, .west, .west, .northWest, .southWest, .east, .west, .west, .southWest, .southWest, .south, .south, .southEast, .east, .southEast, .east, .east, .east, .east, .northWest, .northEast, .southEast, .east, .west, .northWest, .southWest, .southEast, .southEast, .north, .north, .northEast, .north]
def soko3_2Macro147M764State288 : State := {player := 218, boulders := [243, 136, 188, 214, 215, 113, 266, 265, 106, 159, 112, 80, 161], holes := [275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block8_checked : run soko3_2.board soko3_2Macro147M764State256 soko3_2Macro147M764Block8 = some ⟨soko3_2Macro147M764State288, 6, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix8 : List Dir := soko3_2Macro147M764Prefix7 ++ soko3_2Macro147M764Block8
theorem soko3_2Macro147M764_prefix8_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix8 = some ⟨soko3_2Macro147M764State288, 48, 288⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix7 soko3_2Macro147M764Block8
    ⟨soko3_2Macro147M764State256, 42, 256⟩ ⟨soko3_2Macro147M764State288, 6, 32⟩
    soko3_2Macro147M764_prefix7_checked soko3_2Macro147M764_block8_checked
end NetHack.Sokoban.Generated
