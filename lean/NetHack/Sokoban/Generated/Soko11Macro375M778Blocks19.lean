/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks18
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block19 : List Dir := [.north, .northEast, .west, .west, .southWest, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .southWest, .west, .southWest, .east, .east, .west]
def soko1_1Macro375M778State640 : State := {player := 135, boulders := [137, 133, 141, 315, 321], holes := [47, 48, 49]}
theorem soko1_1Macro375M778_block19_checked : run soko1_1.board soko1_1Macro375M778State608 soko1_1Macro375M778Block19 = some ⟨soko1_1Macro375M778State640, 19, 32⟩ := by decide
def soko1_1Macro375M778Prefix19 : List Dir := soko1_1Macro375M778Prefix18 ++ soko1_1Macro375M778Block19
theorem soko1_1Macro375M778_prefix19_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix19 = some ⟨soko1_1Macro375M778State640, 294, 640⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix18 soko1_1Macro375M778Block19
    ⟨soko1_1Macro375M778State608, 275, 608⟩ ⟨soko1_1Macro375M778State640, 19, 32⟩
    soko1_1Macro375M778_prefix18_checked soko1_1Macro375M778_block19_checked
end NetHack.Sokoban.Generated
