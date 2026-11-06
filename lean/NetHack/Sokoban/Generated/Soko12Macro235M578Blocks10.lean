/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks09
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block10 : List Dir := [.north, .north, .northWest, .east, .south, .south, .south, .south, .south, .south, .south, .southWest, .west, .north, .north, .north, .northWest, .east, .east, .southWest, .southEast, .northEast, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south]
def soko1_2Macro235M578State352 : State := {player := 134, boulders := [211, 167, 194, 245, 270, 159, 141, 168, 218], holes := [43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block10_checked : run soko1_2.board soko1_2Macro235M578State320 soko1_2Macro235M578Block10 = some ⟨soko1_2Macro235M578State352, 13, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix10 : List Dir := soko1_2Macro235M578Prefix9 ++ soko1_2Macro235M578Block10
theorem soko1_2Macro235M578_prefix10_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix10 = some ⟨soko1_2Macro235M578State352, 130, 352⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix9 soko1_2Macro235M578Block10
    ⟨soko1_2Macro235M578State320, 117, 320⟩ ⟨soko1_2Macro235M578State352, 13, 32⟩
    soko1_2Macro235M578_prefix9_checked soko1_2Macro235M578_block10_checked
end NetHack.Sokoban.Generated
