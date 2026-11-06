/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko31Witness136.Soko31Macro136M270Blocks02
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block3 : List Dir := [.east, .east, .east, .east, .east, .east, .northEast, .south, .south, .southWest, .east, .east, .east, .west, .west, .northWest, .northWest, .west, .west, .west, .northWest, .north, .north, .northEast, .northEast, .west, .southWest, .northWest, .northEast, .south, .south, .south]
def soko3_1Macro136M270State128 : State := {player := 147, boulders := [176, 271, 61, 62, 64, 65, 177, 206, 264, 265, 209, 267, 213], holes := [309, 310, 311, 312, 313, 314, 315, 316]}
theorem soko3_1Macro136M270_block3_checked : run soko3_1.board soko3_1Macro136M270State96 soko3_1Macro136M270Block3 = some ⟨soko3_1Macro136M270State128, 15, 32⟩ := by decide +kernel
def soko3_1Macro136M270Prefix3 : List Dir := soko3_1Macro136M270Prefix2 ++ soko3_1Macro136M270Block3
theorem soko3_1Macro136M270_prefix3_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix3 = some ⟨soko3_1Macro136M270State128, 56, 128⟩ :=
  run_append_of soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix2 soko3_1Macro136M270Block3
    ⟨soko3_1Macro136M270State96, 41, 96⟩ ⟨soko3_1Macro136M270State128, 15, 32⟩
    soko3_1Macro136M270_prefix2_checked soko3_1Macro136M270_block3_checked
end NetHack.Sokoban.Generated
