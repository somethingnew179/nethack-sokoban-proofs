/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks07
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block8 : List Dir := [.northWest, .east, .south, .south, .south, .south, .south, .south, .south, .south, .south, .southWest, .northWest, .east, .southEast, .north, .north, .north, .north, .north, .north, .north, .north, .north, .northWest, .east, .south, .south, .south, .south, .south, .south]
def soko1_2Macro235M578State288 : State := {player := 186, boulders := [158, 211, 167, 194, 245, 270, 159, 210, 237, 141, 168, 218], holes := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block8_checked : run soko1_2.board soko1_2Macro235M578State256 soko1_2Macro235M578Block8 = some ⟨soko1_2Macro235M578State288, 12, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix8 : List Dir := soko1_2Macro235M578Prefix7 ++ soko1_2Macro235M578Block8
theorem soko1_2Macro235M578_prefix8_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix8 = some ⟨soko1_2Macro235M578State288, 102, 288⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix7 soko1_2Macro235M578Block8
    ⟨soko1_2Macro235M578State256, 90, 256⟩ ⟨soko1_2Macro235M578State288, 12, 32⟩
    soko1_2Macro235M578_prefix7_checked soko1_2Macro235M578_block8_checked
end NetHack.Sokoban.Generated
