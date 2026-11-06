/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko31Witness136.Soko31Macro136M270Blocks04
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block5 : List Dir := [.northEast, .south, .south, .southWest, .east, .east, .east, .west, .west, .northWest, .northWest, .west, .west, .southWest, .southEast, .north, .northWest, .east, .east, .east, .east, .northEast, .south, .south, .southWest, .east, .east, .east, .west, .west, .northWest, .northWest]
def soko3_1Macro136M270State192 : State := {player := 238, boulders := [271, 61, 62, 64, 65, 177, 206, 209, 267, 213], holes := [312, 313, 314, 315, 316]}
theorem soko3_1Macro136M270_block5_checked : run soko3_1.board soko3_1Macro136M270State160 soko3_1Macro136M270Block5 = some ⟨soko3_1Macro136M270State192, 15, 32⟩ := by decide +kernel
def soko3_1Macro136M270Prefix5 : List Dir := soko3_1Macro136M270Prefix4 ++ soko3_1Macro136M270Block5
theorem soko3_1Macro136M270_prefix5_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix5 = some ⟨soko3_1Macro136M270State192, 90, 192⟩ :=
  run_append_of soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix4 soko3_1Macro136M270Block5
    ⟨soko3_1Macro136M270State160, 75, 160⟩ ⟨soko3_1Macro136M270State192, 15, 32⟩
    soko3_1Macro136M270_prefix4_checked soko3_1Macro136M270_block5_checked
end NetHack.Sokoban.Generated
