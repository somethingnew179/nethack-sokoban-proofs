/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks03
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block4 : List Dir := [.west, .west, .south, .south, .south, .southEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .west, .southWest, .west, .west, .west, .west, .west, .northWest, .southWest, .east, .east, .east, .east, .east, .east]
def soko3_2Macro147M764State160 : State := {player := 293, boulders := [294, 136, 113, 266, 265, 241, 214, 135, 106, 159, 112, 80, 161, 188], holes := [274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block4_checked : run soko3_2.board soko3_2Macro147M764State128 soko3_2Macro147M764Block4 = some ⟨soko3_2Macro147M764State160, 11, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix4 : List Dir := soko3_2Macro147M764Prefix3 ++ soko3_2Macro147M764Block4
theorem soko3_2Macro147M764_prefix4_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix4 = some ⟨soko3_2Macro147M764State160, 31, 160⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix3 soko3_2Macro147M764Block4
    ⟨soko3_2Macro147M764State128, 20, 128⟩ ⟨soko3_2Macro147M764State160, 11, 32⟩
    soko3_2Macro147M764_prefix3_checked soko3_2Macro147M764_block4_checked
end NetHack.Sokoban.Generated
