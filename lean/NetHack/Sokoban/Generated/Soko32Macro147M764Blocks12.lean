/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks11
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block12 : List Dir := [.south, .south, .north, .north, .northWest, .northWest, .west, .west, .southWest, .southWest, .south, .south, .southEast, .east, .southEast, .east, .east, .east, .east, .southEast, .north, .north, .northEast, .north, .north, .northWest, .northWest, .southWest, .south, .south, .southEast, .east]
def soko3_2Macro147M764State416 : State := {player := 243, boulders := [244, 267, 188, 214, 113, 266, 265, 106, 159, 112, 80, 161], holes := [276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block12_checked : run soko3_2.board soko3_2Macro147M764State384 soko3_2Macro147M764Block12 = some ⟨soko3_2Macro147M764State416, 7, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix12 : List Dir := soko3_2Macro147M764Prefix11 ++ soko3_2Macro147M764Block12
theorem soko3_2Macro147M764_prefix12_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix12 = some ⟨soko3_2Macro147M764State416, 65, 416⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix11 soko3_2Macro147M764Block12
    ⟨soko3_2Macro147M764State384, 58, 384⟩ ⟨soko3_2Macro147M764State416, 7, 32⟩
    soko3_2Macro147M764_prefix11_checked soko3_2Macro147M764_block12_checked
end NetHack.Sokoban.Generated
