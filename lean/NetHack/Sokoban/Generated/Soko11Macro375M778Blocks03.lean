/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks02
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block3 : List Dir := [.north, .northEast, .northEast, .west, .west, .east, .east, .east, .southEast, .northEast, .west, .west, .north, .north, .northEast, .southEast, .west, .northWest, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .south, .southWest, .east]
def soko1_1Macro375M778State128 : State := {player := 317, boulders := [318, 189, 186, 366, 184, 368, 370, 296, 263, 133, 135, 137, 141, 193, 315, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block3_checked : run soko1_1.board soko1_1Macro375M778State96 soko1_1Macro375M778Block3 = some ⟨soko1_1Macro375M778State128, 16, 32⟩ := by decide
def soko1_1Macro375M778Prefix3 : List Dir := soko1_1Macro375M778Prefix2 ++ soko1_1Macro375M778Block3
theorem soko1_1Macro375M778_prefix3_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix3 = some ⟨soko1_1Macro375M778State128, 52, 128⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix2 soko1_1Macro375M778Block3
    ⟨soko1_1Macro375M778State96, 36, 96⟩ ⟨soko1_1Macro375M778State128, 16, 32⟩
    soko1_1Macro375M778_prefix2_checked soko1_1Macro375M778_block3_checked
end NetHack.Sokoban.Generated
