/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks03
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block4 : List Dir := [.north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .southEast, .south, .southWest, .south, .southEast, .southEast, .southEast, .south, .southEast, .east, .northEast, .north, .north, .northEast, .northEast, .northWest, .northWest, .west, .west, .west]
def soko1_2Macro235M578State160 : State := {player := 189, boulders := [213, 158, 264, 211, 167, 194, 245, 270, 159, 210, 237, 263, 318, 141, 168, 218], holes := [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block4_checked : run soko1_2.board soko1_2Macro235M578State128 soko1_2Macro235M578Block4 = some ⟨soko1_2Macro235M578State160, 8, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix4 : List Dir := soko1_2Macro235M578Prefix3 ++ soko1_2Macro235M578Block4
theorem soko1_2Macro235M578_prefix4_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix4 = some ⟨soko1_2Macro235M578State160, 56, 160⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix3 soko1_2Macro235M578Block4
    ⟨soko1_2Macro235M578State128, 48, 128⟩ ⟨soko1_2Macro235M578State160, 8, 32⟩
    soko1_2Macro235M578_prefix3_checked soko1_2Macro235M578_block4_checked
end NetHack.Sokoban.Generated
