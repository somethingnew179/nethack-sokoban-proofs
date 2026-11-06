/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks15
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block16 : List Dir := [.south, .west, .northEast, .northWest, .southWest, .southWest, .south, .southEast, .east, .north, .west, .west, .west, .west, .northWest, .south, .southEast, .west, .west, .west, .southWest, .north, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south]
def soko1_2Macro235M578State544 : State := {player := 82, boulders := [168, 167, 142], holes := [49]}
theorem soko1_2Macro235M578_block16_checked : run soko1_2.board soko1_2Macro235M578State512 soko1_2Macro235M578Block16 = some ⟨soko1_2Macro235M578State544, 18, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix16 : List Dir := soko1_2Macro235M578Prefix15 ++ soko1_2Macro235M578Block16
theorem soko1_2Macro235M578_prefix16_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix16 = some ⟨soko1_2Macro235M578State544, 218, 544⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix15 soko1_2Macro235M578Block16
    ⟨soko1_2Macro235M578State512, 200, 512⟩ ⟨soko1_2Macro235M578State544, 18, 32⟩
    soko1_2Macro235M578_prefix15_checked soko1_2Macro235M578_block16_checked
end NetHack.Sokoban.Generated
