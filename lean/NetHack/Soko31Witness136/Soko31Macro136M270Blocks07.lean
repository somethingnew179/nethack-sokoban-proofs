/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko31Witness136.Soko31Macro136M270Blocks06
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block7 : List Dir := [.east, .east, .northEast, .south, .south, .southWest, .east, .east, .east, .west, .west, .west, .west, .north, .northEast, .west, .west, .west, .northWest, .southWest, .east, .east, .east, .east, .northEast, .south, .south, .southWest, .east, .east, .east, .east]
def soko3_1Macro136M270State256 : State := {player := 300, boulders := [176, 271, 61, 62, 64, 65, 213], holes := [315, 316]}
theorem soko3_1Macro136M270_block7_checked : run soko3_1.board soko3_1Macro136M270State224 soko3_1Macro136M270Block7 = some ⟨soko3_1Macro136M270State256, 21, 32⟩ := by decide +kernel
def soko3_1Macro136M270Prefix7 : List Dir := soko3_1Macro136M270Prefix6 ++ soko3_1Macro136M270Block7
theorem soko3_1Macro136M270_prefix7_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix7 = some ⟨soko3_1Macro136M270State256, 130, 256⟩ :=
  run_append_of soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix6 soko3_1Macro136M270Block7
    ⟨soko3_1Macro136M270State224, 109, 224⟩ ⟨soko3_1Macro136M270State256, 21, 32⟩
    soko3_1Macro136M270_prefix6_checked soko3_1Macro136M270_block7_checked
end NetHack.Sokoban.Generated
