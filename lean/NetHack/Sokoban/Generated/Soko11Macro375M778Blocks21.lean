/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks20
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block21 : List Dir := [.southEast, .southWest, .north, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .southWest, .west, .southWest, .east, .east, .east, .northEast, .south]
def soko1_1Macro375M778State704 : State := {player := 138, boulders := [164, 140, 315, 321], holes := [48, 49]}
theorem soko1_1Macro375M778_block21_checked : run soko1_1.board soko1_1Macro375M778State672 soko1_1Macro375M778Block21 = some ⟨soko1_1Macro375M778State704, 19, 32⟩ := by decide
def soko1_1Macro375M778Prefix21 : List Dir := soko1_1Macro375M778Prefix20 ++ soko1_1Macro375M778Block21
theorem soko1_1Macro375M778_prefix21_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix21 = some ⟨soko1_1Macro375M778State704, 326, 704⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix20 soko1_1Macro375M778Block21
    ⟨soko1_1Macro375M778State672, 307, 672⟩ ⟨soko1_1Macro375M778State704, 19, 32⟩
    soko1_1Macro375M778_prefix20_checked soko1_1Macro375M778_block21_checked
end NetHack.Sokoban.Generated
