/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks10
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block11 : List Dir := [.west, .northWest, .northWest, .north, .north, .northEast, .northEast, .east, .east, .northEast, .south, .south, .east, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .west, .northWest, .west, .south, .northEast, .east, .northEast, .north, .northWest, .northWest, .southWest, .south]
def soko3_2Macro147M764State384 : State := {player := 189, boulders := [293, 188, 214, 215, 113, 266, 265, 106, 159, 112, 80, 161], holes := [276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block11_checked : run soko3_2.board soko3_2Macro147M764State352 soko3_2Macro147M764Block11 = some ⟨soko3_2Macro147M764State384, 4, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix11 : List Dir := soko3_2Macro147M764Prefix10 ++ soko3_2Macro147M764Block11
theorem soko3_2Macro147M764_prefix11_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix11 = some ⟨soko3_2Macro147M764State384, 58, 384⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix10 soko3_2Macro147M764Block11
    ⟨soko3_2Macro147M764State352, 54, 352⟩ ⟨soko3_2Macro147M764State384, 4, 32⟩
    soko3_2Macro147M764_prefix10_checked soko3_2Macro147M764_block11_checked
end NetHack.Sokoban.Generated
