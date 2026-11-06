/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block13 : List Dir := [.northWest, .northWest, .northWest, .northWest, .west, .west, .southWest, .southWest, .southEast, .east, .east, .east, .east, .west, .west, .west, .west, .northWest, .northEast, .northEast, .east, .east, .southEast, .south, .northEast, .northEast, .southEast, .southEast, .south, .south, .west, .west]
def soko3_2Macro147M764State448 : State := {player := 242, boulders := [270, 214, 215, 267, 113, 266, 265, 106, 159, 112, 80, 161], holes := [276, 277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block13_checked : run soko3_2.board soko3_2Macro147M764State416 soko3_2Macro147M764Block13 = some ⟨soko3_2Macro147M764State448, 3, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix13 : List Dir := soko3_2Macro147M764Prefix12 ++ soko3_2Macro147M764Block13
theorem soko3_2Macro147M764_prefix13_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix13 = some ⟨soko3_2Macro147M764State448, 68, 448⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix12 soko3_2Macro147M764Block13
    ⟨soko3_2Macro147M764State416, 65, 416⟩ ⟨soko3_2Macro147M764State448, 3, 32⟩
    soko3_2Macro147M764_prefix12_checked soko3_2Macro147M764_block13_checked
end NetHack.Sokoban.Generated
