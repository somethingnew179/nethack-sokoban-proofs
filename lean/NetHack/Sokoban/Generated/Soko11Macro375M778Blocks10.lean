/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks09
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block10 : List Dir := [.southWest, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .southEast, .east, .southEast, .northEast]
def soko1_1Macro375M778State352 : State := {player := 269, boulders := [318, 366, 368, 370, 296, 133, 135, 141, 315, 268, 321], holes := [41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block10_checked : run soko1_1.board soko1_1Macro375M778State320 soko1_1Macro375M778Block10 = some ⟨soko1_1Macro375M778State352, 14, 32⟩ := by decide
def soko1_1Macro375M778Prefix10 : List Dir := soko1_1Macro375M778Prefix9 ++ soko1_1Macro375M778Block10
theorem soko1_1Macro375M778_prefix10_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix10 = some ⟨soko1_1Macro375M778State352, 153, 352⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix9 soko1_1Macro375M778Block10
    ⟨soko1_1Macro375M778State320, 139, 320⟩ ⟨soko1_1Macro375M778State352, 14, 32⟩
    soko1_1Macro375M778_prefix9_checked soko1_1Macro375M778_block10_checked
end NetHack.Sokoban.Generated
