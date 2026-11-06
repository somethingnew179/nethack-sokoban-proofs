/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks11
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block12 : List Dir := [.south, .south, .south, .south, .south, .southEast, .southEast, .east, .east, .northEast, .east, .southEast, .southEast, .southWest, .north, .west, .north, .southEast, .northEast, .west, .north, .west, .west, .west, .northWest, .south, .southEast, .west, .west, .west, .southWest, .north]
def soko1_2Macro235M578State416 : State := {player := 212, boulders := [186, 218, 167, 194, 270, 141, 168], holes := [45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block12_checked : run soko1_2.board soko1_2Macro235M578State384 soko1_2Macro235M578Block12 = some ⟨soko1_2Macro235M578State416, 11, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix12 : List Dir := soko1_2Macro235M578Prefix11 ++ soko1_2Macro235M578Block12
theorem soko1_2Macro235M578_prefix12_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix12 = some ⟨soko1_2Macro235M578State416, 157, 416⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix11 soko1_2Macro235M578Block12
    ⟨soko1_2Macro235M578State384, 146, 384⟩ ⟨soko1_2Macro235M578State416, 11, 32⟩
    soko1_2Macro235M578_prefix11_checked soko1_2Macro235M578_block12_checked
end NetHack.Sokoban.Generated
