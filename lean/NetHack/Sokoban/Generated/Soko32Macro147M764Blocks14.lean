/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks13
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block14 : List Dir := [.west, .south, .northEast, .east, .northEast, .north, .northWest, .northWest, .southWest, .south, .south, .south, .east, .southEast, .east, .northWest, .northWest, .northWest, .northWest, .northWest, .west, .west, .southWest, .southWest, .south, .south, .southEast, .east, .southEast, .east, .east, .east]
def soko3_2Macro147M764State480 : State := {player := 293, boulders := [294, 267, 214, 113, 266, 265, 106, 159, 112, 80, 161], holes := [277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block14_checked : run soko3_2.board soko3_2Macro147M764State448 soko3_2Macro147M764Block14 = some ⟨soko3_2Macro147M764State480, 5, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix14 : List Dir := soko3_2Macro147M764Prefix13 ++ soko3_2Macro147M764Block14
theorem soko3_2Macro147M764_prefix14_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix14 = some ⟨soko3_2Macro147M764State480, 73, 480⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix13 soko3_2Macro147M764Block14
    ⟨soko3_2Macro147M764State448, 68, 448⟩ ⟨soko3_2Macro147M764State480, 5, 32⟩
    soko3_2Macro147M764_prefix13_checked soko3_2Macro147M764_block14_checked
end NetHack.Sokoban.Generated
