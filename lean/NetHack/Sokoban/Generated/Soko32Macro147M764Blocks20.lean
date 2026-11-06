/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks19
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block20 : List Dir := [.north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .west, .northWest, .west, .southWest, .southWest, .east, .east, .east, .southEast, .north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest]
def soko3_2Macro147M764State672 : State := {player := 189, boulders := [244, 113, 106, 159, 112, 80, 161], holes := [281, 282, 283]}
theorem soko3_2Macro147M764_block20_checked : run soko3_2.board soko3_2Macro147M764State640 soko3_2Macro147M764Block20 = some ⟨soko3_2Macro147M764State672, 10, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix20 : List Dir := soko3_2Macro147M764Prefix19 ++ soko3_2Macro147M764Block20
theorem soko3_2Macro147M764_prefix20_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix20 = some ⟨soko3_2Macro147M764State672, 115, 672⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix19 soko3_2Macro147M764Block20
    ⟨soko3_2Macro147M764State640, 105, 640⟩ ⟨soko3_2Macro147M764State672, 10, 32⟩
    soko3_2Macro147M764_prefix19_checked soko3_2Macro147M764_block20_checked
end NetHack.Sokoban.Generated
