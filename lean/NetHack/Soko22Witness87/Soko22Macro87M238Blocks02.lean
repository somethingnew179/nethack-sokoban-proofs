/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko22Witness87.Soko22Macro87M238Blocks01
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Block2 : List Dir := [.north, .north, .northEast, .northEast, .northWest, .northWest, .southWest, .south, .south, .north, .northWest, .west, .west, .southWest, .south, .south, .southEast, .east, .northEast, .east, .northEast, .south, .south, .south, .south, .south, .south, .southWest, .east, .north, .north, .north]
def soko2_2Macro87M238State96 : State := {player := 182, boulders := [118, 50, 223, 70, 73, 90, 91, 141, 157, 158, 161], holes := [255, 256, 257, 258, 259, 260]}
theorem soko2_2Macro87M238_block2_checked : run soko2_2.board soko2_2Macro87M238State64 soko2_2Macro87M238Block2 = some ⟨soko2_2Macro87M238State96, 10, 32⟩ := by decide
def soko2_2Macro87M238Prefix2 : List Dir := soko2_2Macro87M238Prefix1 ++ soko2_2Macro87M238Block2
theorem soko2_2Macro87M238_prefix2_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix2 = some ⟨soko2_2Macro87M238State96, 35, 96⟩ :=
  run_append_of soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix1 soko2_2Macro87M238Block2
    ⟨soko2_2Macro87M238State64, 25, 64⟩ ⟨soko2_2Macro87M238State96, 10, 32⟩
    soko2_2Macro87M238_prefix1_checked soko2_2Macro87M238_block2_checked
end NetHack.Sokoban.Generated
