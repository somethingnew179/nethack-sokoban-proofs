/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks00
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block1 : List Dir := [.northWest, .northWest, .southWest, .east, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .west, .northWest, .southWest, .southEast, .north, .northWest, .east, .southEast, .east, .east, .northEast, .north, .north, .northWest, .northWest, .north, .north, .north, .west]
def soko1_1Macro375M778State64 : State := {player := 186, boulders := [185, 368, 370, 296, 263, 133, 135, 137, 139, 141, 212, 188, 191, 193, 315, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block1_checked : run soko1_1.board soko1_1Macro375M778State32 soko1_1Macro375M778Block1 = some ⟨soko1_1Macro375M778State64, 12, 32⟩ := by decide
def soko1_1Macro375M778Prefix1 : List Dir := soko1_1Macro375M778Prefix0 ++ soko1_1Macro375M778Block1
theorem soko1_1Macro375M778_prefix1_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix1 = some ⟨soko1_1Macro375M778State64, 19, 64⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix0 soko1_1Macro375M778Block1
    ⟨soko1_1Macro375M778State32, 7, 32⟩ ⟨soko1_1Macro375M778State64, 12, 32⟩
    soko1_1Macro375M778_prefix0_checked soko1_1Macro375M778_block1_checked
end NetHack.Sokoban.Generated
