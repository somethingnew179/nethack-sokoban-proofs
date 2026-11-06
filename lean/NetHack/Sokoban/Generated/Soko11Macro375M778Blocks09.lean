/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks08
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block9 : List Dir := [.southEast, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .south, .southEast, .northEast, .west]
def soko1_1Macro375M778State320 : State := {player := 266, boulders := [265, 318, 366, 368, 370, 296, 133, 135, 141, 315, 268, 321], holes := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block9_checked : run soko1_1.board soko1_1Macro375M778State288 soko1_1Macro375M778Block9 = some ⟨soko1_1Macro375M778State320, 15, 32⟩ := by decide
def soko1_1Macro375M778Prefix9 : List Dir := soko1_1Macro375M778Prefix8 ++ soko1_1Macro375M778Block9
theorem soko1_1Macro375M778_prefix9_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix9 = some ⟨soko1_1Macro375M778State320, 139, 320⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix8 soko1_1Macro375M778Block9
    ⟨soko1_1Macro375M778State288, 124, 288⟩ ⟨soko1_1Macro375M778State320, 15, 32⟩
    soko1_1Macro375M778_prefix8_checked soko1_1Macro375M778_block9_checked
end NetHack.Sokoban.Generated
