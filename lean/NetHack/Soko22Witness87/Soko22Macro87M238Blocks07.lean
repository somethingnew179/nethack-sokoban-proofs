/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko22Witness87.Soko22Macro87M238Blocks06
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Block7 : List Dir := [.west, .east, .northEast, .north, .northWest, .west, .southWest, .south, .south, .south, .south, .south, .southWest, .east]
def soko2_2Macro87M238State238 : State := {player := 248, boulders := [185, 118, 50, 73, 90], holes := []}
theorem soko2_2Macro87M238_block7_checked : run soko2_2.board soko2_2Macro87M238State224 soko2_2Macro87M238Block7 = some ⟨soko2_2Macro87M238State238, 6, 14⟩ := by decide
def soko2_2Macro87M238Prefix7 : List Dir := soko2_2Macro87M238Prefix6 ++ soko2_2Macro87M238Block7
theorem soko2_2Macro87M238_prefix7_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix7 = some ⟨soko2_2Macro87M238State238, 87, 238⟩ :=
  run_append_of soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix6 soko2_2Macro87M238Block7
    ⟨soko2_2Macro87M238State224, 81, 224⟩ ⟨soko2_2Macro87M238State238, 6, 14⟩
    soko2_2Macro87M238_prefix6_checked soko2_2Macro87M238_block7_checked
end NetHack.Sokoban.Generated
