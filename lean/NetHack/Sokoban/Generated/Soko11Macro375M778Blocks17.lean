/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block17 : List Dir := [.east, .east, .southEast, .north, .north, .north, .north, .northEast, .west, .west, .southWest, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south]
def soko1_1Macro375M778State576 : State := {player := 85, boulders := [318, 133, 135, 141, 315, 321], holes := [46, 47, 48, 49]}
theorem soko1_1Macro375M778_block17_checked : run soko1_1.board soko1_1Macro375M778State544 soko1_1Macro375M778Block17 = some ⟨soko1_1Macro375M778State576, 22, 32⟩ := by decide
def soko1_1Macro375M778Prefix17 : List Dir := soko1_1Macro375M778Prefix16 ++ soko1_1Macro375M778Block17
theorem soko1_1Macro375M778_prefix17_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix17 = some ⟨soko1_1Macro375M778State576, 259, 576⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix16 soko1_1Macro375M778Block17
    ⟨soko1_1Macro375M778State544, 237, 544⟩ ⟨soko1_1Macro375M778State576, 22, 32⟩
    soko1_1Macro375M778_prefix16_checked soko1_1Macro375M778_block17_checked
end NetHack.Sokoban.Generated
