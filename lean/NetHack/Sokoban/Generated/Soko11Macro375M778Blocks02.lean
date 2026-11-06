/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks01
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block2 : List Dir := [.west, .south, .east, .northEast, .south, .south, .south, .south, .southWest, .east, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .west, .west, .southWest, .north, .east, .east, .east, .east, .northEast, .north, .north, .northWest, .northWest]
def soko1_1Macro375M778State96 : State := {player := 265, boulders := [366, 184, 368, 370, 296, 263, 133, 135, 137, 139, 141, 188, 191, 193, 315, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block2_checked : run soko1_1.board soko1_1Macro375M778State64 soko1_1Macro375M778Block2 = some ⟨soko1_1Macro375M778State96, 17, 32⟩ := by decide
def soko1_1Macro375M778Prefix2 : List Dir := soko1_1Macro375M778Prefix1 ++ soko1_1Macro375M778Block2
theorem soko1_1Macro375M778_prefix2_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix2 = some ⟨soko1_1Macro375M778State96, 36, 96⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix1 soko1_1Macro375M778Block2
    ⟨soko1_1Macro375M778State64, 19, 64⟩ ⟨soko1_1Macro375M778State96, 17, 32⟩
    soko1_1Macro375M778_prefix1_checked soko1_1Macro375M778_block2_checked
end NetHack.Sokoban.Generated
