/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks15
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block16 : List Dir := [.north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .south, .southEast, .southEast, .south, .southWest, .west, .west, .west, .southWest, .northWest, .east, .east, .east]
def soko1_1Macro375M778State544 : State := {player := 368, boulders := [369, 318, 133, 135, 141, 315, 321], holes := [45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block16_checked : run soko1_1.board soko1_1Macro375M778State512 soko1_1Macro375M778Block16 = some ⟨soko1_1Macro375M778State544, 11, 32⟩ := by decide
def soko1_1Macro375M778Prefix16 : List Dir := soko1_1Macro375M778Prefix15 ++ soko1_1Macro375M778Block16
theorem soko1_1Macro375M778_prefix16_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix16 = some ⟨soko1_1Macro375M778State544, 237, 544⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix15 soko1_1Macro375M778Block16
    ⟨soko1_1Macro375M778State512, 226, 512⟩ ⟨soko1_1Macro375M778State544, 11, 32⟩
    soko1_1Macro375M778_prefix15_checked soko1_1Macro375M778_block16_checked
end NetHack.Sokoban.Generated
