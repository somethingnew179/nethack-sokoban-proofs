/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block13 : List Dir := [.north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .southEast, .southEast, .east, .east, .northEast, .east, .southEast, .southWest, .north, .northEast, .west, .west, .west, .northWest, .south, .southEast, .west, .west, .west]
def soko1_2Macro235M578State448 : State := {player := 213, boulders := [212, 167, 194, 270, 141, 168], holes := [46, 47, 48, 49]}
theorem soko1_2Macro235M578_block13_checked : run soko1_2.board soko1_2Macro235M578State416 soko1_2Macro235M578Block13 = some ⟨soko1_2Macro235M578State448, 15, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix13 : List Dir := soko1_2Macro235M578Prefix12 ++ soko1_2Macro235M578Block13
theorem soko1_2Macro235M578_prefix13_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix13 = some ⟨soko1_2Macro235M578State448, 172, 448⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix12 soko1_2Macro235M578Block13
    ⟨soko1_2Macro235M578State416, 157, 416⟩ ⟨soko1_2Macro235M578State448, 15, 32⟩
    soko1_2Macro235M578_prefix12_checked soko1_2Macro235M578_block13_checked
end NetHack.Sokoban.Generated
