/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks04
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block5 : List Dir := [.west, .southWest, .north, .north, .north, .south, .south, .south, .southEast, .southWest, .west, .west, .southWest, .northWest, .east, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south]
def soko1_1Macro375M778State192 : State := {player := 85, boulders := [291, 318, 366, 184, 368, 370, 296, 263, 133, 135, 141, 193, 315, 266, 268, 321], holes := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block5_checked : run soko1_1.board soko1_1Macro375M778State160 soko1_1Macro375M778Block5 = some ⟨soko1_1Macro375M778State192, 16, 32⟩ := by decide
def soko1_1Macro375M778Prefix5 : List Dir := soko1_1Macro375M778Prefix4 ++ soko1_1Macro375M778Block5
theorem soko1_1Macro375M778_prefix5_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix5 = some ⟨soko1_1Macro375M778State192, 82, 192⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix4 soko1_1Macro375M778Block5
    ⟨soko1_1Macro375M778State160, 66, 160⟩ ⟨soko1_1Macro375M778State192, 16, 32⟩
    soko1_1Macro375M778_prefix4_checked soko1_1Macro375M778_block5_checked
end NetHack.Sokoban.Generated
