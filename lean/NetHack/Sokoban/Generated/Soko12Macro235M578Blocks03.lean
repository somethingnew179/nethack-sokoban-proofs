/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks02
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block3 : List Dir := [.south, .southWest, .southWest, .south, .southWest, .west, .northWest, .north, .northWest, .west, .north, .north, .south, .southEast, .southEast, .south, .southEast, .east, .northEast, .north, .north, .northEast, .northEast, .northWest, .northWest, .west, .west, .west, .southWest, .west, .southWest, .north]
def soko1_2Macro235M578State128 : State := {player := 212, boulders := [186, 187, 158, 264, 211, 167, 194, 245, 270, 159, 210, 237, 263, 318, 141, 168, 218], holes := [35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_2Macro235M578_block3_checked : run soko1_2.board soko1_2Macro235M578State96 soko1_2Macro235M578Block3 = some ⟨soko1_2Macro235M578State128, 4, 32⟩ := by decide +kernel
def soko1_2Macro235M578Prefix3 : List Dir := soko1_2Macro235M578Prefix2 ++ soko1_2Macro235M578Block3
theorem soko1_2Macro235M578_prefix3_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix3 = some ⟨soko1_2Macro235M578State128, 48, 128⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix2 soko1_2Macro235M578Block3
    ⟨soko1_2Macro235M578State96, 44, 96⟩ ⟨soko1_2Macro235M578State128, 4, 32⟩
    soko1_2Macro235M578_prefix2_checked soko1_2Macro235M578_block3_checked
end NetHack.Sokoban.Generated
