/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks14
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block15 : List Dir := [.south, .southEast, .west, .west, .west, .southWest, .north, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .southEast, .southEast, .east, .east, .northEast, .northEast, .north, .east, .south, .north, .northEast, .southEast]
def soko1_2Macro235M578State512 : State := {player := 143, boulders := [193, 142, 194, 168], holes := [48, 49]}
theorem soko1_2Macro235M578_block15_checked : run soko1_2.board soko1_2Macro235M578State480 soko1_2Macro235M578Block15 = some ⟨soko1_2Macro235M578State512, 14, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix15 : List Dir := soko1_2Macro235M578Prefix14 ++ soko1_2Macro235M578Block15
theorem soko1_2Macro235M578_prefix15_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix15 = some ⟨soko1_2Macro235M578State512, 200, 512⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix14 soko1_2Macro235M578Block15
    ⟨soko1_2Macro235M578State480, 186, 480⟩ ⟨soko1_2Macro235M578State512, 14, 32⟩
    soko1_2Macro235M578_prefix14_checked soko1_2Macro235M578_block15_checked
end NetHack.Sokoban.Generated
