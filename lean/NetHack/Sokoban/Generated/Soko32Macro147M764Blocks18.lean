/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks17
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block18 : List Dir := [.southWest, .south, .east, .northWest, .northEast, .east, .southEast, .southEast, .east, .west, .northWest, .west, .northWest, .southWest, .south, .southEast, .east, .east, .southEast, .north, .north, .southWest, .west, .northWest, .northWest, .northEast, .east, .southEast, .east, .northWest, .northWest, .north]
def soko3_2Macro147M764State608 : State := {player := 163, boulders := [244, 267, 291, 113, 106, 159, 112, 80, 161], holes := [279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block18_checked : run soko3_2.board soko3_2Macro147M764State576 soko3_2Macro147M764Block18 = some ⟨soko3_2Macro147M764State608, 7, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix18 : List Dir := soko3_2Macro147M764Prefix17 ++ soko3_2Macro147M764Block18
theorem soko3_2Macro147M764_prefix18_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix18 = some ⟨soko3_2Macro147M764State608, 98, 608⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix17 soko3_2Macro147M764Block18
    ⟨soko3_2Macro147M764State576, 91, 576⟩ ⟨soko3_2Macro147M764State608, 7, 32⟩
    soko3_2Macro147M764_prefix17_checked soko3_2Macro147M764_block18_checked
end NetHack.Sokoban.Generated
