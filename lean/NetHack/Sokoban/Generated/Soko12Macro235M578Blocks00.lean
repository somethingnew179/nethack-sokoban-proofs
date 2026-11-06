/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Maps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block0 : List Dir := [.north, .east, .east, .east, .southEast, .north, .north, .north, .north, .east, .north, .east, .north, .north, .west, .north, .west, .west, .west, .southWest, .west, .west, .west, .north, .south, .south, .north, .northWest, .west, .north, .northWest, .northEast]
def soko1_2Macro235M578State32 : State := {player := 106, boulders := [132, 264, 160, 211, 189, 167, 194, 245, 270, 108, 159, 187, 210, 237, 263, 265, 318, 141, 168, 218], holes := [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block0_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Block0 = some ⟨soko1_2Macro235M578State32, 19, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix0 : List Dir := soko1_2Macro235M578Block0
theorem soko1_2Macro235M578_prefix0_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix0 = some ⟨soko1_2Macro235M578State32, 19, 32⟩ := soko1_2Macro235M578_block0_checked
end NetHack.Sokoban.Generated
