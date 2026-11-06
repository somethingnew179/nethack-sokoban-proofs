/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Maps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block0 : List Dir := [.west, .west, .west, .southWest, .west, .west, .west, .southWest, .southWest, .south, .southWest, .southEast, .east, .east, .east, .east, .east, .southEast, .east, .south, .east, .west, .northWest, .southWest, .east, .east, .east, .west, .northWest, .northWest, .north, .northEast]
def soko3_1Macro136M270State32 : State := {player := 182, boulders := [271, 240, 90, 61, 62, 64, 65, 177, 205, 206, 263, 264, 265, 209, 267, 211, 241, 213], holes := [304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316]}
theorem soko3_1Macro136M270_block0_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Block0 = some ⟨soko3_1Macro136M270State32, 13, 32⟩ := by decide +kernel
def soko3_1Macro136M270Prefix0 : List Dir := soko3_1Macro136M270Block0
theorem soko3_1Macro136M270_prefix0_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix0 = some ⟨soko3_1Macro136M270State32, 13, 32⟩ := soko3_1Macro136M270_block0_checked
end NetHack.Sokoban.Generated
