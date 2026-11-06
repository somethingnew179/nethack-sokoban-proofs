/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Maps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block0 : List Dir := [.east, .east, .east, .east, .southEast, .southEast, .south, .southEast, .south, .southWest, .southWest, .southWest, .south, .west, .east, .southEast, .east, .east, .east, .southWest, .southWest, .southWest, .west, .west, .southWest, .northWest, .east, .east, .east, .southEast, .northEast, .north]
def soko1_1Macro375M778State32 : State := {player := 345, boulders := [370, 296, 263, 133, 135, 137, 139, 141, 186, 212, 188, 191, 193, 315, 317, 266, 268, 321], holes := [33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]}
theorem soko1_1Macro375M778_block0_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Block0 = some ⟨soko1_1Macro375M778State32, 7, 32⟩ := by decide
def soko1_1Macro375M778Prefix0 : List Dir := soko1_1Macro375M778Block0
theorem soko1_1Macro375M778_prefix0_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix0 = some ⟨soko1_1Macro375M778State32, 7, 32⟩ := soko1_1Macro375M778_block0_checked
end NetHack.Sokoban.Generated
