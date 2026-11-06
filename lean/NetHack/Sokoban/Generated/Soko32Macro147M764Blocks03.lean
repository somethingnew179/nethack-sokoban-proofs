/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks02
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block3 : List Dir := [.southWest, .west, .east, .northEast, .north, .northWest, .northWest, .north, .northWest, .northWest, .west, .southWest, .southWest, .southWest, .south, .south, .southEast, .east, .southEast, .east, .southEast, .north, .east, .east, .east, .northEast, .northEast, .west, .north, .north, .northWest, .north]
def soko3_2Macro147M764State128 : State := {player := 139, boulders := [113, 243, 266, 288, 265, 241, 214, 135, 106, 159, 112, 138, 80, 161, 188], holes := [273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block3_checked : run soko3_2.board soko3_2Macro147M764State96 soko3_2Macro147M764Block3 = some ⟨soko3_2Macro147M764State128, 4, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix3 : List Dir := soko3_2Macro147M764Prefix2 ++ soko3_2Macro147M764Block3
theorem soko3_2Macro147M764_prefix3_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix3 = some ⟨soko3_2Macro147M764State128, 20, 128⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix2 soko3_2Macro147M764Block3
    ⟨soko3_2Macro147M764State96, 16, 96⟩ ⟨soko3_2Macro147M764State128, 4, 32⟩
    soko3_2Macro147M764_prefix2_checked soko3_2Macro147M764_block3_checked
end NetHack.Sokoban.Generated
