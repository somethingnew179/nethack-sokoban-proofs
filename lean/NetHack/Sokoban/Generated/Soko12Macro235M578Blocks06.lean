/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks05
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block6 : List Dir := [.southEast, .southEast, .south, .southWest, .southWest, .south, .southWest, .west, .northWest, .north, .northEast, .west, .west, .southWest, .north, .north, .north, .south, .south, .southEast, .southEast, .southEast, .east, .northEast, .north, .north, .northEast, .northEast, .northWest, .northWest, .west, .west]
def soko1_2Macro235M578State224 : State := {player := 190, boulders := [213, 158, 264, 211, 167, 194, 245, 270, 159, 210, 237, 263, 141, 168, 218], holes := [37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block6_checked : run soko1_2.board soko1_2Macro235M578State192 soko1_2Macro235M578Block6 = some ⟨soko1_2Macro235M578State224, 6, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix6 : List Dir := soko1_2Macro235M578Prefix5 ++ soko1_2Macro235M578Block6
theorem soko1_2Macro235M578_prefix6_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix6 = some ⟨soko1_2Macro235M578State224, 72, 224⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix5 soko1_2Macro235M578Block6
    ⟨soko1_2Macro235M578State192, 66, 192⟩ ⟨soko1_2Macro235M578State224, 6, 32⟩
    soko1_2Macro235M578_prefix5_checked soko1_2Macro235M578_block6_checked
end NetHack.Sokoban.Generated
