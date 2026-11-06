/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks03
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block4 : List Dir := [.north, .north, .north, .northEast, .east, .northEast, .north, .north, .northWest, .southWest, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .north, .north, .northEast, .east, .southEast, .north, .north, .north, .northEast]
def soko1_1Macro375M778State160 : State := {player := 113, boulders := [112, 291, 318, 186, 366, 184, 368, 370, 296, 263, 133, 135, 141, 193, 315, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block4_checked : run soko1_1.board soko1_1Macro375M778State128 soko1_1Macro375M778Block4 = some ⟨soko1_1Macro375M778State160, 14, 32⟩ := by decide
def soko1_1Macro375M778Prefix4 : List Dir := soko1_1Macro375M778Prefix3 ++ soko1_1Macro375M778Block4
theorem soko1_1Macro375M778_prefix4_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix4 = some ⟨soko1_1Macro375M778State160, 66, 160⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix3 soko1_1Macro375M778Block4
    ⟨soko1_1Macro375M778State128, 52, 128⟩ ⟨soko1_1Macro375M778State160, 14, 32⟩
    soko1_1Macro375M778_prefix3_checked soko1_1Macro375M778_block4_checked
end NetHack.Sokoban.Generated
