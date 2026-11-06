/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko22Witness87.Soko22Macro87M238Blocks00
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Block1 : List Dir := [.south, .west, .southWest, .south, .south, .south, .south, .south, .southWest, .east, .west, .northWest, .northWest, .west, .northWest, .northEast, .northEast, .northEast, .east, .northEast, .south, .south, .south, .south, .south, .south, .southWest, .east, .north, .north, .north, .north]
def soko2_2Macro87M238State64 : State := {player := 160, boulders := [118, 50, 223, 70, 71, 73, 90, 91, 141, 157, 158, 161], holes := [254, 255, 256, 257, 258, 259, 260]}
theorem soko2_2Macro87M238_block1_checked : run soko2_2.board soko2_2Macro87M238State32 soko2_2Macro87M238Block1 = some ⟨soko2_2Macro87M238State64, 15, 32⟩ := by decide
def soko2_2Macro87M238Prefix1 : List Dir := soko2_2Macro87M238Prefix0 ++ soko2_2Macro87M238Block1
theorem soko2_2Macro87M238_prefix1_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix1 = some ⟨soko2_2Macro87M238State64, 25, 64⟩ :=
  run_append_of soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix0 soko2_2Macro87M238Block1
    ⟨soko2_2Macro87M238State32, 10, 32⟩ ⟨soko2_2Macro87M238State64, 15, 32⟩
    soko2_2Macro87M238_prefix0_checked soko2_2Macro87M238_block1_checked
end NetHack.Sokoban.Generated
