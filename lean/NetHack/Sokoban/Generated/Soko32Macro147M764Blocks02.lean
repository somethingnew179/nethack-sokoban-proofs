/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks01
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block2 : List Dir := [.northWest, .north, .northWest, .northWest, .west, .southWest, .southWest, .southWest, .southEast, .east, .east, .southEast, .south, .southEast, .southWest, .north, .west, .west, .northWest, .northWest, .north, .north, .northEast, .northEast, .east, .northEast, .southEast, .south, .southEast, .south, .southEast, .southEast]
def soko3_2Macro147M764State96 : State := {player := 269, boulders := [288, 265, 241, 293, 214, 135, 106, 159, 112, 138, 80, 139, 161, 188, 244], holes := [273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block2_checked : run soko3_2.board soko3_2Macro147M764State64 soko3_2Macro147M764Block2 = some ⟨soko3_2Macro147M764State96, 2, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix2 : List Dir := soko3_2Macro147M764Prefix1 ++ soko3_2Macro147M764Block2
theorem soko3_2Macro147M764_prefix2_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix2 = some ⟨soko3_2Macro147M764State96, 16, 96⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix1 soko3_2Macro147M764Block2
    ⟨soko3_2Macro147M764State64, 14, 64⟩ ⟨soko3_2Macro147M764State96, 2, 32⟩
    soko3_2Macro147M764_prefix1_checked soko3_2Macro147M764_block2_checked
end NetHack.Sokoban.Generated
