/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks21
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block22 : List Dir := [.north, .north, .southWest, .northWest, .northEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .west, .northWest, .northWest, .northWest, .northWest, .west, .northWest, .southWest, .east, .east, .east, .northEast, .south, .south, .southEast, .south]
def soko3_2Macro147M764State736 : State := {player := 241, boulders := [214, 113, 106, 112, 80], holes := [283]}
theorem soko3_2Macro147M764_block22_checked : run soko3_2.board soko3_2Macro147M764State704 soko3_2Macro147M764Block22 = some ⟨soko3_2Macro147M764State736, 10, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix22 : List Dir := soko3_2Macro147M764Prefix21 ++ soko3_2Macro147M764Block22
theorem soko3_2Macro147M764_prefix22_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix22 = some ⟨soko3_2Macro147M764State736, 136, 736⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix21 soko3_2Macro147M764Block22
    ⟨soko3_2Macro147M764State704, 126, 704⟩ ⟨soko3_2Macro147M764State736, 10, 32⟩
    soko3_2Macro147M764_prefix21_checked soko3_2Macro147M764_block22_checked
end NetHack.Sokoban.Generated
