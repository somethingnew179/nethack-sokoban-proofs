/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Maps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block0 : List Dir := [.southEast, .east, .east, .east, .east, .south, .south, .north, .northEast, .southEast, .south, .west, .northEast, .northWest, .west, .west, .west, .west, .west, .west, .west, .southWest, .south, .south, .south, .east, .north, .east, .east, .west, .southWest, .southWest]
def soko3_2Macro147M764State32 : State := {player := 183, boulders := [135, 106, 159, 112, 138, 80, 139, 161, 188, 211, 215, 239, 244, 267, 270, 289], holes := [272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block0_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Block0 = some ⟨soko3_2Macro147M764State32, 6, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix0 : List Dir := soko3_2Macro147M764Block0
theorem soko3_2Macro147M764_prefix0_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix0 = some ⟨soko3_2Macro147M764State32, 6, 32⟩ := soko3_2Macro147M764_block0_checked
end NetHack.Sokoban.Generated
