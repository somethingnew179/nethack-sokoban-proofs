/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks10
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block11 : List Dir := [.west, .west, .west, .southWest, .north, .north, .north, .northWest, .east, .east, .east, .southEast, .north, .north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .southWest, .southWest, .southWest, .southEast]
def soko1_1Macro375M778State384 : State := {player := 266, boulders := [318, 366, 368, 370, 296, 133, 135, 141, 315, 321], holes := [42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block11_checked : run soko1_1.board soko1_1Macro375M778State352 soko1_1Macro375M778Block11 = some ⟨soko1_1Macro375M778State384, 17, 32⟩ := by decide
def soko1_1Macro375M778Prefix11 : List Dir := soko1_1Macro375M778Prefix10 ++ soko1_1Macro375M778Block11
theorem soko1_1Macro375M778_prefix11_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix11 = some ⟨soko1_1Macro375M778State384, 170, 384⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix10 soko1_1Macro375M778Block11
    ⟨soko1_1Macro375M778State352, 153, 352⟩ ⟨soko1_1Macro375M778State384, 17, 32⟩
    soko1_1Macro375M778_prefix10_checked soko1_1Macro375M778_block11_checked
end NetHack.Sokoban.Generated
