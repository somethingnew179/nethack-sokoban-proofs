/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko22Witness87.Soko22Macro87M238Blocks03
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Block4 : List Dir := [.west, .north, .northEast, .north, .northEast, .northEast, .northWest, .west, .southWest, .southWest, .southWest, .southEast, .east, .southEast, .east, .northEast, .northWest, .west, .south, .south, .southWest, .east, .east, .east, .north, .north, .north, .north, .north, .northWest, .southWest, .south]
def soko2_2Macro87M238State160 : State := {player := 158, boulders := [180, 118, 50, 73, 90, 91, 141, 157, 161], holes := [257, 258, 259, 260]}
theorem soko2_2Macro87M238_block4_checked : run soko2_2.board soko2_2Macro87M238State128 soko2_2Macro87M238Block4 = some ⟨soko2_2Macro87M238State160, 8, 32⟩ := by decide
def soko2_2Macro87M238Prefix4 : List Dir := soko2_2Macro87M238Prefix3 ++ soko2_2Macro87M238Block4
theorem soko2_2Macro87M238_prefix4_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix4 = some ⟨soko2_2Macro87M238State160, 54, 160⟩ :=
  run_append_of soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix3 soko2_2Macro87M238Block4
    ⟨soko2_2Macro87M238State128, 46, 128⟩ ⟨soko2_2Macro87M238State160, 8, 32⟩
    soko2_2Macro87M238_prefix3_checked soko2_2Macro87M238_block4_checked
end NetHack.Sokoban.Generated
