/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block17 : List Dir := [.north, .north, .northEast, .north, .north, .northWest, .northWest, .southWest, .south, .south, .southEast, .east, .northWest, .northWest, .north, .northEast, .southEast, .southEast, .south, .south, .west, .west, .west, .northWest, .southWest, .south, .north, .northEast, .southEast, .south, .north, .northWest]
def soko3_2Macro147M764State576 : State := {player := 214, boulders := [293, 291, 270, 113, 266, 106, 159, 112, 80, 161], holes := [278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block17_checked : run soko3_2.board soko3_2Macro147M764State544 soko3_2Macro147M764Block17 = some ⟨soko3_2Macro147M764State576, 6, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix17 : List Dir := soko3_2Macro147M764Prefix16 ++ soko3_2Macro147M764Block17
theorem soko3_2Macro147M764_prefix17_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix17 = some ⟨soko3_2Macro147M764State576, 91, 576⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix16 soko3_2Macro147M764Block17
    ⟨soko3_2Macro147M764State544, 85, 544⟩ ⟨soko3_2Macro147M764State576, 6, 32⟩
    soko3_2Macro147M764_prefix16_checked soko3_2Macro147M764_block17_checked
end NetHack.Sokoban.Generated
