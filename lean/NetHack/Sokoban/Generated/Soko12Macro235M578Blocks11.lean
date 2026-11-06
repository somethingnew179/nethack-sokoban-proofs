/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks10
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block11 : List Dir := [.south, .south, .south, .southWest, .north, .northWest, .east, .southEast, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .southWest, .north, .northWest, .east, .southEast, .north, .north, .north, .north, .northWest, .east]
def soko1_2Macro235M578State384 : State := {player := 30, boulders := [167, 194, 245, 270, 141, 168, 218], holes := [45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block11_checked : run soko1_2.board soko1_2Macro235M578State352 soko1_2Macro235M578Block11 = some ⟨soko1_2Macro235M578State384, 16, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix11 : List Dir := soko1_2Macro235M578Prefix10 ++ soko1_2Macro235M578Block11
theorem soko1_2Macro235M578_prefix11_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix11 = some ⟨soko1_2Macro235M578State384, 146, 384⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix10 soko1_2Macro235M578Block11
    ⟨soko1_2Macro235M578State352, 130, 352⟩ ⟨soko1_2Macro235M578State384, 16, 32⟩
    soko1_2Macro235M578_prefix10_checked soko1_2Macro235M578_block11_checked
end NetHack.Sokoban.Generated
