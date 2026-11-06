/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko22Witness87.Soko22Macro87M238Blocks02
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Block3 : List Dir := [.north, .north, .north, .north, .northWest, .northWest, .southWest, .east, .northEast, .south, .south, .northWest, .west, .northWest, .southWest, .south, .south, .southEast, .east, .northEast, .east, .northEast, .south, .south, .south, .south, .south, .south, .southWest, .east, .west, .west]
def soko2_2Macro87M238State128 : State := {player := 246, boulders := [118, 50, 223, 73, 90, 91, 141, 157, 158, 161], holes := [256, 257, 258, 259, 260]}
theorem soko2_2Macro87M238_block3_checked : run soko2_2.board soko2_2Macro87M238State96 soko2_2Macro87M238Block3 = some ⟨soko2_2Macro87M238State128, 11, 32⟩ := by decide
def soko2_2Macro87M238Prefix3 : List Dir := soko2_2Macro87M238Prefix2 ++ soko2_2Macro87M238Block3
theorem soko2_2Macro87M238_prefix3_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix3 = some ⟨soko2_2Macro87M238State128, 46, 128⟩ :=
  run_append_of soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix2 soko2_2Macro87M238Block3
    ⟨soko2_2Macro87M238State96, 35, 96⟩ ⟨soko2_2Macro87M238State128, 11, 32⟩
    soko2_2Macro87M238_prefix2_checked soko2_2Macro87M238_block3_checked
end NetHack.Sokoban.Generated
