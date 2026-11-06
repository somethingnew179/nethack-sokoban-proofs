/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko31Witness136.Soko31Macro136M270Blocks05
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block6 : List Dir := [.west, .northWest, .north, .west, .south, .southWest, .east, .east, .east, .east, .east, .northEast, .south, .south, .southWest, .east, .east, .east, .northWest, .northWest, .northWest, .northWest, .south, .southEast, .west, .west, .west, .northWest, .southWest, .east, .east, .east]
def soko3_1Macro136M270State224 : State := {player := 237, boulders := [238, 176, 271, 61, 62, 64, 65, 267, 213], holes := [313, 314, 315, 316]}
theorem soko3_1Macro136M270_block6_checked : run soko3_1.board soko3_1Macro136M270State192 soko3_1Macro136M270Block6 = some ⟨soko3_1Macro136M270State224, 19, 32⟩ := by decide +kernel
def soko3_1Macro136M270Prefix6 : List Dir := soko3_1Macro136M270Prefix5 ++ soko3_1Macro136M270Block6
theorem soko3_1Macro136M270_prefix6_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix6 = some ⟨soko3_1Macro136M270State224, 109, 224⟩ :=
  run_append_of soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix5 soko3_1Macro136M270Block6
    ⟨soko3_1Macro136M270State192, 90, 192⟩ ⟨soko3_1Macro136M270State224, 19, 32⟩
    soko3_1Macro136M270_prefix5_checked soko3_1Macro136M270_block6_checked
end NetHack.Sokoban.Generated
