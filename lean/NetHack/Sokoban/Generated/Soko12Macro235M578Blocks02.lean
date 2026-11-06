/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks01
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block2 : List Dir := [.east, .northEast, .northWest, .south, .southEast, .west, .west, .west, .southWest, .north, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .south, .southEast, .east, .east, .east, .northEast, .east, .southEast, .southEast]
def soko1_2Macro235M578State96 : State := {player := 246, boulders := [187, 158, 264, 211, 167, 194, 245, 270, 159, 210, 237, 263, 265, 318, 141, 168, 218], holes := [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block2_checked : run soko1_2.board soko1_2Macro235M578State64 soko1_2Macro235M578Block2 = some ⟨soko1_2Macro235M578State96, 12, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix2 : List Dir := soko1_2Macro235M578Prefix1 ++ soko1_2Macro235M578Block2
theorem soko1_2Macro235M578_prefix2_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix2 = some ⟨soko1_2Macro235M578State96, 44, 96⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix1 soko1_2Macro235M578Block2
    ⟨soko1_2Macro235M578State64, 32, 64⟩ ⟨soko1_2Macro235M578State96, 12, 32⟩
    soko1_2Macro235M578_prefix1_checked soko1_2Macro235M578_block2_checked
end NetHack.Sokoban.Generated
