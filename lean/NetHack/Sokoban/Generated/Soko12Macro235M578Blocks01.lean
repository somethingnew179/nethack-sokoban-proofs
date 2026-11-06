/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks00
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block1 : List Dir := [.south, .east, .east, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .south, .west, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .south, .south, .southEast, .north, .east]
def soko1_2Macro235M578State64 : State := {player := 214, boulders := [187, 158, 264, 211, 189, 167, 194, 245, 270, 159, 210, 237, 263, 265, 318, 141, 168, 218], holes := [34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block1_checked : run soko1_2.board soko1_2Macro235M578State32 soko1_2Macro235M578Block1 = some ⟨soko1_2Macro235M578State64, 13, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix1 : List Dir := soko1_2Macro235M578Prefix0 ++ soko1_2Macro235M578Block1
theorem soko1_2Macro235M578_prefix1_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix1 = some ⟨soko1_2Macro235M578State64, 32, 64⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix0 soko1_2Macro235M578Block1
    ⟨soko1_2Macro235M578State32, 19, 32⟩ ⟨soko1_2Macro235M578State64, 13, 32⟩
    soko1_2Macro235M578_prefix0_checked soko1_2Macro235M578_block1_checked
end NetHack.Sokoban.Generated
