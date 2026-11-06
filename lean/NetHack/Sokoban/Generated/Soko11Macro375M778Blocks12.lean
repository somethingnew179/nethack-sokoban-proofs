/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks11
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block12 : List Dir := [.east, .east, .east, .east, .southEast, .west, .west, .west, .west, .west, .northWest, .southWest, .southEast, .north, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .south, .south]
def soko1_1Macro375M778State416 : State := {player := 137, boulders := [59, 318, 366, 368, 370, 133, 135, 141, 315, 321], holes := [42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block12_checked : run soko1_1.board soko1_1Macro375M778State384 soko1_1Macro375M778Block12 = some ⟨soko1_1Macro375M778State416, 18, 32⟩ := by decide
def soko1_1Macro375M778Prefix12 : List Dir := soko1_1Macro375M778Prefix11 ++ soko1_1Macro375M778Block12
theorem soko1_1Macro375M778_prefix12_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix12 = some ⟨soko1_1Macro375M778State416, 188, 416⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix11 soko1_1Macro375M778Block12
    ⟨soko1_1Macro375M778State384, 170, 384⟩ ⟨soko1_1Macro375M778State416, 18, 32⟩
    soko1_1Macro375M778_prefix11_checked soko1_1Macro375M778_block12_checked
end NetHack.Sokoban.Generated
