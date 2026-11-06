/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko31Witness136.Soko31Macro136M270Blocks07
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_1Macro136M270Block8 : List Dir := [.northWest, .northEast, .south, .southWest, .east, .north, .north, .northWest, .northEast, .south, .south, .south, .southWest, .east]
def soko3_1Macro136M270State270 : State := {player := 300, boulders := [176, 61, 62, 64, 65], holes := []}
theorem soko3_1Macro136M270_block8_checked : run soko3_1.board soko3_1Macro136M270State256 soko3_1Macro136M270Block8 = some ⟨soko3_1Macro136M270State270, 6, 14⟩ := by decide +kernel
def soko3_1Macro136M270Prefix8 : List Dir := soko3_1Macro136M270Prefix7 ++ soko3_1Macro136M270Block8
theorem soko3_1Macro136M270_prefix8_checked : run soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix8 = some ⟨soko3_1Macro136M270State270, 136, 270⟩ :=
  run_append_of soko3_1.board soko3_1.initial soko3_1Macro136M270Prefix7 soko3_1Macro136M270Block8
    ⟨soko3_1Macro136M270State256, 130, 256⟩ ⟨soko3_1Macro136M270State270, 6, 14⟩
    soko3_1Macro136M270_prefix7_checked soko3_1Macro136M270_block8_checked
end NetHack.Sokoban.Generated
