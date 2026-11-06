/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks19
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block20 : List Dir := [.west, .northWest, .southWest, .east, .east, .northEast, .east, .east, .east, .east, .east, .east, .southEast, .west, .northWest, .west, .west, .west, .southWest, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south]
def soko1_1Macro375M778State672 : State := {player := 265, boulders := [291, 140, 135, 315, 321], holes := [47, 48, 49]}
theorem soko1_1Macro375M778_block20_checked : run soko1_1.board soko1_1Macro375M778State640 soko1_1Macro375M778Block20 = some ⟨soko1_1Macro375M778State672, 13, 32⟩ := by decide
def soko1_1Macro375M778Prefix20 : List Dir := soko1_1Macro375M778Prefix19 ++ soko1_1Macro375M778Block20
theorem soko1_1Macro375M778_prefix20_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix20 = some ⟨soko1_1Macro375M778State672, 307, 672⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix19 soko1_1Macro375M778Block20
    ⟨soko1_1Macro375M778State640, 294, 640⟩ ⟨soko1_1Macro375M778State672, 13, 32⟩
    soko1_1Macro375M778_prefix19_checked soko1_1Macro375M778_block20_checked
end NetHack.Sokoban.Generated
