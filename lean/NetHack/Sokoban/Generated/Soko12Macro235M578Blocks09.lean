/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks08
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block9 : List Dir := [.south, .south, .southWest, .northWest, .east, .southEast, .north, .north, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .southWest, .west, .north, .northWest, .east, .east, .southWest, .southEast, .northEast, .north, .north]
def soko1_2Macro235M578State320 : State := {player := 108, boulders := [82, 211, 167, 194, 245, 270, 159, 210, 141, 168, 218], holes := [41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block9_checked : run soko1_2.board soko1_2Macro235M578State288 soko1_2Macro235M578Block9 = some ⟨soko1_2Macro235M578State320, 15, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix9 : List Dir := soko1_2Macro235M578Prefix8 ++ soko1_2Macro235M578Block9
theorem soko1_2Macro235M578_prefix9_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix9 = some ⟨soko1_2Macro235M578State320, 117, 320⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix8 soko1_2Macro235M578Block9
    ⟨soko1_2Macro235M578State288, 102, 288⟩ ⟨soko1_2Macro235M578State320, 15, 32⟩
    soko1_2Macro235M578_prefix8_checked soko1_2Macro235M578_block9_checked
end NetHack.Sokoban.Generated
