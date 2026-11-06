/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko31Witness136.Soko31Macro136M270Blocks03
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block4 : List Dir := [.south, .south, .southWest, .east, .east, .east, .east, .east, .east, .northEast, .south, .south, .southWest, .east, .east, .east, .west, .west, .northWest, .northWest, .west, .west, .west, .southWest, .southEast, .north, .northWest, .east, .east, .east, .east, .east]
def soko3_1Macro136M270State160 : State := {player := 239, boulders := [240, 271, 61, 62, 64, 65, 177, 206, 265, 209, 267, 213], holes := [310, 311, 312, 313, 314, 315, 316]}
theorem soko3_1Macro136M270_block4_checked : run soko3_1.board soko3_1Macro136M270State128 soko3_1Macro136M270Block4 = some ⟨soko3_1Macro136M270State160, 19, 32⟩ := by decide +kernel
def soko3_1Macro136M270Prefix4 : List Dir := soko3_1Macro136M270Prefix3 ++ soko3_1Macro136M270Block4
theorem soko3_1Macro136M270_prefix4_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix4 = some ⟨soko3_1Macro136M270State160, 75, 160⟩ :=
  run_append_of soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix3 soko3_1Macro136M270Block4
    ⟨soko3_1Macro136M270State128, 56, 128⟩ ⟨soko3_1Macro136M270State160, 19, 32⟩
    soko3_1Macro136M270_prefix3_checked soko3_1Macro136M270_block4_checked
end NetHack.Sokoban.Generated
