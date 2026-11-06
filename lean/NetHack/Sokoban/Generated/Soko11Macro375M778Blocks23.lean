/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks22
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block23 : List Dir := [.south, .south, .southEast, .east, .east, .southEast, .west, .west, .northWest, .south, .south, .south, .southEast, .west, .west, .west, .northWest, .south, .south, .south, .southEast, .southWest, .north, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north]
def soko1_1Macro375M778State768 : State := {player := 190, boulders := [164, 315, 321], holes := [49]}
theorem soko1_1Macro375M778_block23_checked : run soko1_1.board soko1_1Macro375M778State736 soko1_1Macro375M778Block23 = some ⟨soko1_1Macro375M778State768, 19, 32⟩ := by decide
def soko1_1Macro375M778Prefix23 : List Dir := soko1_1Macro375M778Prefix22 ++ soko1_1Macro375M778Block23
theorem soko1_1Macro375M778_prefix23_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix23 = some ⟨soko1_1Macro375M778State768, 368, 768⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix22 soko1_1Macro375M778Block23
    ⟨soko1_1Macro375M778State736, 349, 736⟩ ⟨soko1_1Macro375M778State768, 19, 32⟩
    soko1_1Macro375M778_prefix22_checked soko1_1Macro375M778_block23_checked
end NetHack.Sokoban.Generated
