/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks06
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block7 : List Dir := [.southEast, .southEast, .east, .southEast, .northEast, .west, .west, .west, .southWest, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .south, .southWest, .southEast, .north]
def soko1_1Macro375M778State256 : State := {player := 291, boulders := [265, 318, 366, 368, 370, 296, 263, 133, 135, 141, 315, 266, 268, 321], holes := [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block7_checked : run soko1_1.board soko1_1Macro375M778State224 soko1_1Macro375M778Block7 = some ⟨soko1_1Macro375M778State256, 12, 32⟩ := by decide
def soko1_1Macro375M778Prefix7 : List Dir := soko1_1Macro375M778Prefix6 ++ soko1_1Macro375M778Block7
theorem soko1_1Macro375M778_prefix7_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix7 = some ⟨soko1_1Macro375M778State256, 108, 256⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix6 soko1_1Macro375M778Block7
    ⟨soko1_1Macro375M778State224, 96, 224⟩ ⟨soko1_1Macro375M778State256, 12, 32⟩
    soko1_1Macro375M778_prefix6_checked soko1_1Macro375M778_block7_checked
end NetHack.Sokoban.Generated
