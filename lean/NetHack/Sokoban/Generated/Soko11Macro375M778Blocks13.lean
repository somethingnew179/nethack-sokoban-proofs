/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block13 : List Dir := [.southEast, .southWest, .southWest, .southWest, .south, .southEast, .southEast, .south, .south, .southWest, .northWest, .east, .southEast, .north, .north, .north, .north, .northEast, .west, .west, .southWest, .north, .north, .north, .northWest, .east, .east, .south, .southWest, .south, .southEast, .southEast]
def soko1_1Macro375M778State448 : State := {player := 319, boulders := [189, 59, 318, 366, 368, 133, 135, 141, 315, 321], holes := [42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block13_checked : run soko1_1.board soko1_1Macro375M778State416 soko1_1Macro375M778Block13 = some ⟨soko1_1Macro375M778State448, 12, 32⟩ := by decide
def soko1_1Macro375M778Prefix13 : List Dir := soko1_1Macro375M778Prefix12 ++ soko1_1Macro375M778Block13
theorem soko1_1Macro375M778_prefix13_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix13 = some ⟨soko1_1Macro375M778State448, 200, 448⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix12 soko1_1Macro375M778Block13
    ⟨soko1_1Macro375M778State416, 188, 416⟩ ⟨soko1_1Macro375M778State448, 12, 32⟩
    soko1_1Macro375M778_prefix12_checked soko1_1Macro375M778_block13_checked
end NetHack.Sokoban.Generated
