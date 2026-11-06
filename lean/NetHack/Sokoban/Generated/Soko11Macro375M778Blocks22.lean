/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks21
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block22 : List Dir := [.south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .southEast, .southWest, .north, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east]
def soko1_1Macro375M778State736 : State := {player := 33, boulders := [140, 315, 321], holes := [49]}
theorem soko1_1Macro375M778_block22_checked : run soko1_1.board soko1_1Macro375M778State704 soko1_1Macro375M778Block22 = some ⟨soko1_1Macro375M778State736, 23, 32⟩ := by decide
def soko1_1Macro375M778Prefix22 : List Dir := soko1_1Macro375M778Prefix21 ++ soko1_1Macro375M778Block22
theorem soko1_1Macro375M778_prefix22_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix22 = some ⟨soko1_1Macro375M778State736, 349, 736⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix21 soko1_1Macro375M778Block22
    ⟨soko1_1Macro375M778State704, 326, 704⟩ ⟨soko1_1Macro375M778State736, 23, 32⟩
    soko1_1Macro375M778_prefix21_checked soko1_1Macro375M778_block22_checked
end NetHack.Sokoban.Generated
