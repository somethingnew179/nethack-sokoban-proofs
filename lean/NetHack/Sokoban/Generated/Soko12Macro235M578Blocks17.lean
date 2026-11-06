/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks16
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block17 : List Dir := [.south, .south, .south, .southEast, .southEast, .east, .east, .northEast, .northEast, .northEast, .south, .southWest, .southEast, .northEast, .west, .west, .west, .west, .northWest, .south, .southEast, .west, .west, .west, .southWest, .north, .north, .north, .north, .north, .north, .north]
def soko1_2Macro235M578State576 : State := {player := 56, boulders := [30, 168, 142], holes := [49]}
theorem soko1_2Macro235M578_block17_checked : run soko1_2.board soko1_2Macro235M578State544 soko1_2Macro235M578Block17 = some ⟨soko1_2Macro235M578State576, 16, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix17 : List Dir := soko1_2Macro235M578Prefix16 ++ soko1_2Macro235M578Block17
theorem soko1_2Macro235M578_prefix17_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix17 = some ⟨soko1_2Macro235M578State576, 234, 576⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix16 soko1_2Macro235M578Block17
    ⟨soko1_2Macro235M578State544, 218, 544⟩ ⟨soko1_2Macro235M578State576, 16, 32⟩
    soko1_2Macro235M578_prefix16_checked soko1_2Macro235M578_block17_checked
end NetHack.Sokoban.Generated
