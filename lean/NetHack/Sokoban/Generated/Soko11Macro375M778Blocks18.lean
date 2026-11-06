/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks17
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block18 : List Dir := [.south, .south, .southEast, .southWest, .southWest, .southWest, .south, .south, .south, .east, .northEast, .south, .south, .south, .southEast, .west, .west, .west, .west, .northWest, .southWest, .southEast, .north, .northWest, .east, .east, .east, .east, .southEast, .north, .north, .north]
def soko1_1Macro375M778State608 : State := {player := 319, boulders := [293, 133, 135, 141, 315, 321], holes := [46, 47, 48, 49]}
theorem soko1_1Macro375M778_block18_checked : run soko1_1.board soko1_1Macro375M778State576 soko1_1Macro375M778Block18 = some ⟨soko1_1Macro375M778State608, 16, 32⟩ := by decide
def soko1_1Macro375M778Prefix18 : List Dir := soko1_1Macro375M778Prefix17 ++ soko1_1Macro375M778Block18
theorem soko1_1Macro375M778_prefix18_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix18 = some ⟨soko1_1Macro375M778State608, 275, 608⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix17 soko1_1Macro375M778Block18
    ⟨soko1_1Macro375M778State576, 259, 576⟩ ⟨soko1_1Macro375M778State608, 16, 32⟩
    soko1_1Macro375M778_prefix17_checked soko1_1Macro375M778_block18_checked
end NetHack.Sokoban.Generated
