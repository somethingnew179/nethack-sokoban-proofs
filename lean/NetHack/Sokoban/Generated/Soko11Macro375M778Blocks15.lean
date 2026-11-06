/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks14
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block15 : List Dir := [.south, .south, .southEast, .south, .southWest, .northWest, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .west, .southWest, .northWest, .east, .east, .east, .southEast]
def soko1_1Macro375M778State512 : State := {player := 216, boulders := [190, 318, 366, 133, 135, 141, 315, 321], holes := [44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block15_checked : run soko1_1.board soko1_1Macro375M778State480 soko1_1Macro375M778Block15 = some ⟨soko1_1Macro375M778State512, 12, 32⟩ := by decide
def soko1_1Macro375M778Prefix15 : List Dir := soko1_1Macro375M778Prefix14 ++ soko1_1Macro375M778Block15
theorem soko1_1Macro375M778_prefix15_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix15 = some ⟨soko1_1Macro375M778State512, 226, 512⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix14 soko1_1Macro375M778Block15
    ⟨soko1_1Macro375M778State480, 214, 480⟩ ⟨soko1_1Macro375M778State512, 12, 32⟩
    soko1_1Macro375M778_prefix14_checked soko1_1Macro375M778_block15_checked
end NetHack.Sokoban.Generated
