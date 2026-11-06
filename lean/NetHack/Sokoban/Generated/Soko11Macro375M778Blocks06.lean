/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks05
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block6 : List Dir := [.south, .south, .southEast, .southWest, .west, .west, .west, .west, .southWest, .northWest, .east, .east, .east, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south]
def soko1_1Macro375M778State224 : State := {player := 137, boulders := [291, 318, 366, 368, 370, 296, 263, 133, 135, 141, 193, 315, 266, 268, 321], holes := [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block6_checked : run soko1_1.board soko1_1Macro375M778State192 soko1_1Macro375M778Block6 = some ⟨soko1_1Macro375M778State224, 14, 32⟩ := by decide
def soko1_1Macro375M778Prefix6 : List Dir := soko1_1Macro375M778Prefix5 ++ soko1_1Macro375M778Block6
theorem soko1_1Macro375M778_prefix6_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix6 = some ⟨soko1_1Macro375M778State224, 96, 224⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix5 soko1_1Macro375M778Block6
    ⟨soko1_1Macro375M778State192, 82, 192⟩ ⟨soko1_1Macro375M778State224, 14, 32⟩
    soko1_1Macro375M778_prefix5_checked soko1_1Macro375M778_block6_checked
end NetHack.Sokoban.Generated
