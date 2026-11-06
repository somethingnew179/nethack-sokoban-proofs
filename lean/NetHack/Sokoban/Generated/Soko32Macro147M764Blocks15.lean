/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko32Macro147M764Blocks14
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko3_2Macro147M764Block15 : List Dir := [.east, .southEast, .north, .north, .northEast, .north, .north, .northWest, .northWest, .southWest, .south, .south, .southEast, .east, .northWest, .northWest, .northWest, .northWest, .west, .west, .southWest, .southWest, .southEast, .east, .east, .east, .east, .north, .northEast, .northEast, .southEast, .southEast]
def soko3_2Macro147M764State512 : State := {player := 192, boulders := [215, 244, 267, 113, 266, 265, 106, 159, 112, 80, 161], holes := [277, 278, 279, 280, 281, 282, 283]}
theorem soko3_2Macro147M764_block15_checked : run soko3_2.board soko3_2Macro147M764State480 soko3_2Macro147M764Block15 = some ⟨soko3_2Macro147M764State512, 5, 32⟩ := by decide +kernel
def soko3_2Macro147M764Prefix15 : List Dir := soko3_2Macro147M764Prefix14 ++ soko3_2Macro147M764Block15
theorem soko3_2Macro147M764_prefix15_checked : run soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix15 = some ⟨soko3_2Macro147M764State512, 78, 512⟩ :=
  run_append_of soko3_2.board soko3_2.initial soko3_2Macro147M764Prefix14 soko3_2Macro147M764Block15
    ⟨soko3_2Macro147M764State480, 73, 480⟩ ⟨soko3_2Macro147M764State512, 5, 32⟩
    soko3_2Macro147M764_prefix14_checked soko3_2Macro147M764_block15_checked
end NetHack.Sokoban.Generated
