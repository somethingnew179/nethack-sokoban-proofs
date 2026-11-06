/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks00
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block1 : List Dir := [.southEast, .east, .east, .east, .south, .south, .east, .southEast, .east, .northEast, .northWest, .west, .south, .west, .northWest, .northWest, .west, .west, .northWest, .northEast, .northEast, .east, .northEast, .southEast, .south, .southEast, .south, .southEast, .southEast, .east, .northWest, .northWest]
def soko3_2Macro147M764State64 : State := {player := 216, boulders := [241, 293, 291, 214, 135, 106, 159, 112, 138, 80, 139, 161, 188, 244, 289], holes := [273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block1_checked : run soko3_2.board soko3_2Macro147M764State32 soko3_2Macro147M764Block1 = some ⟨soko3_2Macro147M764State64, 8, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix1 : List Dir := soko3_2Macro147M764Prefix0 ++ soko3_2Macro147M764Block1
theorem soko3_2Macro147M764_prefix1_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix1 = some ⟨soko3_2Macro147M764State64, 14, 64⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix0 soko3_2Macro147M764Block1
    ⟨soko3_2Macro147M764State32, 6, 32⟩ ⟨soko3_2Macro147M764State64, 8, 32⟩
    soko3_2Macro147M764_prefix0_checked soko3_2Macro147M764_block1_checked
end NetHack.Sokoban.Generated
