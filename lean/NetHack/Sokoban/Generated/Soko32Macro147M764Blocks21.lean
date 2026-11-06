/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks20
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block21 : List Dir := [.north, .northEast, .southEast, .southEast, .south, .south, .southWest, .east, .northWest, .northWest, .northWest, .northWest, .northWest, .southWest, .east, .northEast, .south, .south, .southEast, .south, .southWest, .northWest, .north, .east, .northEast, .south, .south, .south, .southWest, .east, .east, .southEast]
def soko3_2Macro147M764State704 : State := {player := 321, boulders := [295, 113, 106, 159, 112, 80], holes := [282, 283]}
theorem soko3_2Macro147M764_block21_checked : run soko3_2.board soko3_2Macro147M764State672 soko3_2Macro147M764Block21 = some ⟨soko3_2Macro147M764State704, 11, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix21 : List Dir := soko3_2Macro147M764Prefix20 ++ soko3_2Macro147M764Block21
theorem soko3_2Macro147M764_prefix21_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix21 = some ⟨soko3_2Macro147M764State704, 126, 704⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix20 soko3_2Macro147M764Block21
    ⟨soko3_2Macro147M764State672, 115, 672⟩ ⟨soko3_2Macro147M764State704, 11, 32⟩
    soko3_2Macro147M764_prefix20_checked soko3_2Macro147M764_block21_checked
end NetHack.Sokoban.Generated
