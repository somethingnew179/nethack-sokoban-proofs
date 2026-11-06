/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko31Witness136.Soko31Macro136M270Blocks01
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block2 : List Dir := [.west, .west, .west, .northWest, .northEast, .south, .southWest, .east, .east, .east, .east, .east, .east, .northEast, .south, .south, .southWest, .east, .east, .east, .west, .west, .northWest, .northWest, .west, .west, .west, .west, .southWest, .southEast, .north, .northWest]
def soko3_1Macro136M270State96 : State := {player := 233, boulders := [234, 271, 90, 61, 62, 64, 65, 177, 206, 264, 265, 209, 267, 213], holes := [308, 309, 310, 311, 312, 313, 314, 315, 316]}
theorem soko3_1Macro136M270_block2_checked : run soko3_1.board soko3_1Macro136M270State64 soko3_1Macro136M270Block2 = some ⟨soko3_1Macro136M270State96, 13, 32⟩ := by decide +kernel
def soko3_1Macro136M270Prefix2 : List Dir := soko3_1Macro136M270Prefix1 ++ soko3_1Macro136M270Block2
theorem soko3_1Macro136M270_prefix2_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix2 = some ⟨soko3_1Macro136M270State96, 41, 96⟩ :=
  run_append_of soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix1 soko3_1Macro136M270Block2
    ⟨soko3_1Macro136M270State64, 28, 64⟩ ⟨soko3_1Macro136M270State96, 13, 32⟩
    soko3_1Macro136M270_prefix1_checked soko3_1Macro136M270_block2_checked
end NetHack.Sokoban.Generated
