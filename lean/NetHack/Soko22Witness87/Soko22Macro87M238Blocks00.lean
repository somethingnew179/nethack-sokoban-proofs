/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Maps
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Block0 : List Dir := [.north, .west, .west, .south, .east, .east, .northWest, .northWest, .northEast, .east, .south, .south, .southWest, .east, .west, .northWest, .northWest, .west, .northWest, .north, .north, .north, .north, .north, .northEast, .east, .east, .east, .northEast, .east, .southEast, .south]
def soko2_2Macro87M238State32 : State := {player := 74, boulders := [96, 50, 223, 70, 71, 73, 90, 91, 115, 138, 141, 157, 158, 161], holes := [252, 253, 254, 255, 256, 257, 258, 259, 260]}
theorem soko2_2Macro87M238_block0_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Block0 = some ⟨soko2_2Macro87M238State32, 10, 32⟩ := by decide
def soko2_2Macro87M238Prefix0 : List Dir := soko2_2Macro87M238Block0
theorem soko2_2Macro87M238_prefix0_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix0 = some ⟨soko2_2Macro87M238State32, 10, 32⟩ := soko2_2Macro87M238_block0_checked
end NetHack.Sokoban.Generated
