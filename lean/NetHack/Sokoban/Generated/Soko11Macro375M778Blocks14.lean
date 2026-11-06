/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks13
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block14 : List Dir := [.south, .southWest, .west, .southWest, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .north, .northEast, .west, .west, .southWest, .north, .north, .north, .east, .east, .northEast, .north, .north, .north, .northWest, .north, .northWest, .east, .south, .south]
def soko1_1Macro375M778State480 : State := {player := 85, boulders := [187, 189, 318, 366, 133, 135, 141, 315, 321], holes := [43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block14_checked : run soko1_1.board soko1_1Macro375M778State448 soko1_1Macro375M778Block14 = some ⟨soko1_1Macro375M778State480, 14, 32⟩ := by decide
def soko1_1Macro375M778Prefix14 : List Dir := soko1_1Macro375M778Prefix13 ++ soko1_1Macro375M778Block14
theorem soko1_1Macro375M778_prefix14_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix14 = some ⟨soko1_1Macro375M778State480, 214, 480⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix13 soko1_1Macro375M778Block14
    ⟨soko1_1Macro375M778State448, 200, 448⟩ ⟨soko1_1Macro375M778State480, 14, 32⟩
    soko1_1Macro375M778_prefix13_checked soko1_1Macro375M778_block14_checked
end NetHack.Sokoban.Generated
