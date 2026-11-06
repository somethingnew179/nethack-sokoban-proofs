/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko22Witness87.Soko22Macro87M238Blocks04
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Block5 : List Dir := [.south, .south, .south, .southWest, .east, .east, .east, .north, .north, .north, .north, .north, .north, .northWest, .northWest, .west, .south, .south, .north, .north, .northWest, .southWest, .south, .south, .southEast, .east, .northEast, .south, .south, .south, .south, .south]
def soko2_2Macro87M238State192 : State := {player := 224, boulders := [246, 118, 50, 73, 90, 141, 157, 161], holes := [258, 259, 260]}
theorem soko2_2Macro87M238_block5_checked : run soko2_2.board soko2_2Macro87M238State160 soko2_2Macro87M238Block5 = some ⟨soko2_2Macro87M238State192, 14, 32⟩ := by decide
def soko2_2Macro87M238Prefix5 : List Dir := soko2_2Macro87M238Prefix4 ++ soko2_2Macro87M238Block5
theorem soko2_2Macro87M238_prefix5_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix5 = some ⟨soko2_2Macro87M238State192, 68, 192⟩ :=
  run_append_of soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix4 soko2_2Macro87M238Block5
    ⟨soko2_2Macro87M238State160, 54, 160⟩ ⟨soko2_2Macro87M238State192, 14, 32⟩
    soko2_2Macro87M238_prefix4_checked soko2_2Macro87M238_block5_checked
end NetHack.Sokoban.Generated
