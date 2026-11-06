/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks18
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block19 : List Dir := [.northEast, .southEast, .southEast, .south, .south, .west, .west, .west, .south, .northEast, .southEast, .east, .west, .northWest, .southWest, .southWest, .east, .northWest, .northWest, .northWest, .west, .west, .southWest, .southEast, .east, .southEast, .east, .northEast, .southEast, .east, .southEast, .north]
def soko3_2Macro147M764State640 : State := {player := 295, boulders := [269, 292, 113, 106, 159, 112, 80, 161], holes := [280, 281, 282, 283]}
theorem soko3_2Macro147M764_block19_checked : run soko3_2.board soko3_2Macro147M764State608 soko3_2Macro147M764Block19 = some ⟨soko3_2Macro147M764State640, 7, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix19 : List Dir := soko3_2Macro147M764Prefix18 ++ soko3_2Macro147M764Block19
theorem soko3_2Macro147M764_prefix19_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix19 = some ⟨soko3_2Macro147M764State640, 105, 640⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix18 soko3_2Macro147M764Block19
    ⟨soko3_2Macro147M764State608, 98, 608⟩ ⟨soko3_2Macro147M764State640, 7, 32⟩
    soko3_2Macro147M764_prefix18_checked soko3_2Macro147M764_block19_checked
end NetHack.Sokoban.Generated
