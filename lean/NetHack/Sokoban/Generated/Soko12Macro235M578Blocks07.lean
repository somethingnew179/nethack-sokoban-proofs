/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks06
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block7 : List Dir := [.west, .southWest, .west, .southWest, .north, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .south, .south, .south, .southEast, .southWest, .north, .north, .north, .north, .north, .north, .north, .north, .north]
def soko1_2Macro235M578State256 : State := {player := 56, boulders := [30, 158, 211, 167, 194, 245, 270, 159, 210, 237, 263, 141, 168, 218], holes := [38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block7_checked : run soko1_2.board soko1_2Macro235M578State224 soko1_2Macro235M578Block7 = some ⟨soko1_2Macro235M578State256, 18, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix7 : List Dir := soko1_2Macro235M578Prefix6 ++ soko1_2Macro235M578Block7
theorem soko1_2Macro235M578_prefix7_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix7 = some ⟨soko1_2Macro235M578State256, 90, 256⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix6 soko1_2Macro235M578Block7
    ⟨soko1_2Macro235M578State224, 72, 224⟩ ⟨soko1_2Macro235M578State256, 18, 32⟩
    soko1_2Macro235M578_prefix6_checked soko1_2Macro235M578_block7_checked
end NetHack.Sokoban.Generated
