/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko31Witness136.Soko31Macro136M270Blocks00
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block1 : List Dir := [.southEast, .south, .south, .southWest, .east, .east, .west, .northWest, .northWest, .north, .east, .northEast, .south, .south, .south, .southWest, .east, .east, .northWest, .north, .northWest, .south, .south, .southWest, .east, .east, .east, .west, .west, .northWest, .northWest, .west]
def soko3_1Macro136M270State64 : State := {player := 237, boulders := [271, 90, 61, 62, 64, 65, 177, 205, 206, 263, 264, 265, 209, 267, 213], holes := [307, 308, 309, 310, 311, 312, 313, 314, 315, 316]}
theorem soko3_1Macro136M270_block1_checked : run soko3_1.board soko3_1Macro136M270State32 soko3_1Macro136M270Block1 = some ⟨soko3_1Macro136M270State64, 15, 32⟩ := by decide +kernel
def soko3_1Macro136M270Prefix1 : List Dir := soko3_1Macro136M270Prefix0 ++ soko3_1Macro136M270Block1
theorem soko3_1Macro136M270_prefix1_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix1 = some ⟨soko3_1Macro136M270State64, 28, 64⟩ :=
  run_append_of soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix0 soko3_1Macro136M270Block1
    ⟨soko3_1Macro136M270State32, 13, 32⟩ ⟨soko3_1Macro136M270State64, 15, 32⟩
    soko3_1Macro136M270_prefix0_checked soko3_1Macro136M270_block1_checked
end NetHack.Sokoban.Generated
