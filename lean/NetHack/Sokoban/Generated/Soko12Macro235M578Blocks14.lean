/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks13
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block14 : List Dir := [.southWest, .north, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .southEast, .southEast, .east, .east, .northEast, .southEast, .south, .southEast, .southWest, .north, .north, .north, .northEast, .west, .west, .west, .northWest]
def soko1_2Macro235M578State480 : State := {player := 163, boulders := [189, 167, 194, 141, 168], holes := [47, 48, 49]}
theorem soko1_2Macro235M578_block14_checked : run soko1_2.board soko1_2Macro235M578State448 soko1_2Macro235M578Block14 = some ⟨soko1_2Macro235M578State480, 14, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix14 : List Dir := soko1_2Macro235M578Prefix13 ++ soko1_2Macro235M578Block14
theorem soko1_2Macro235M578_prefix14_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix14 = some ⟨soko1_2Macro235M578State480, 186, 480⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix13 soko1_2Macro235M578Block14
    ⟨soko1_2Macro235M578State448, 172, 448⟩ ⟨soko1_2Macro235M578State480, 14, 32⟩
    soko1_2Macro235M578_prefix13_checked soko1_2Macro235M578_block14_checked
end NetHack.Sokoban.Generated
