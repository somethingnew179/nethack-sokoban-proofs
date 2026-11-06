/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks07
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block8 : List Dir := [.north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .southWest, .southWest, .northWest, .east, .east]
def soko1_1Macro375M778State288 : State := {player := 264, boulders := [265, 318, 366, 368, 370, 296, 133, 135, 141, 315, 266, 268, 321], holes := [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block8_checked : run soko1_1.board soko1_1Macro375M778State256 soko1_1Macro375M778Block8 = some ⟨soko1_1Macro375M778State288, 16, 32⟩ := by decide
def soko1_1Macro375M778Prefix8 : List Dir := soko1_1Macro375M778Prefix7 ++ soko1_1Macro375M778Block8
theorem soko1_1Macro375M778_prefix8_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix8 = some ⟨soko1_1Macro375M778State288, 124, 288⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix7 soko1_1Macro375M778Block8
    ⟨soko1_1Macro375M778State256, 108, 256⟩ ⟨soko1_1Macro375M778State288, 16, 32⟩
    soko1_1Macro375M778_prefix7_checked soko1_1Macro375M778_block8_checked
end NetHack.Sokoban.Generated
