/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks04
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block5 : List Dir := [.southWest, .west, .southWest, .north, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .south, .south, .south, .southEast, .south, .south, .east, .north, .northWest, .north, .northEast, .east, .east, .northEast, .east]
def soko1_2Macro235M578State192 : State := {player := 192, boulders := [319, 158, 264, 211, 167, 194, 245, 270, 159, 210, 237, 263, 141, 168, 218], holes := [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block5_checked : run soko1_2.board soko1_2Macro235M578State160 soko1_2Macro235M578Block5 = some ⟨soko1_2Macro235M578State192, 10, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix5 : List Dir := soko1_2Macro235M578Prefix4 ++ soko1_2Macro235M578Block5
theorem soko1_2Macro235M578_prefix5_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix5 = some ⟨soko1_2Macro235M578State192, 66, 192⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix4 soko1_2Macro235M578Block5
    ⟨soko1_2Macro235M578State160, 56, 160⟩ ⟨soko1_2Macro235M578State192, 10, 32⟩
    soko1_2Macro235M578_prefix4_checked soko1_2Macro235M578_block5_checked
end NetHack.Sokoban.Generated
