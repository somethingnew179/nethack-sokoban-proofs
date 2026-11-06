/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Soko22Witness87.Soko22Macro87M238Blocks05
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko2_2Macro87M238Block6 : List Dir := [.southWest, .east, .east, .east, .north, .north, .northWest, .northWest, .northWest, .southWest, .east, .northEast, .south, .south, .south, .south, .southWest, .east, .east, .east, .north, .north, .north, .north, .north, .north, .northEast, .east, .southEast, .south, .south, .west]
def soko2_2Macro87M238State224 : State := {player := 162, boulders := [185, 118, 50, 73, 90, 161], holes := [260]}
theorem soko2_2Macro87M238_block6_checked : run soko2_2.board soko2_2Macro87M238State192 soko2_2Macro87M238Block6 = some ⟨soko2_2Macro87M238State224, 13, 32⟩ := by decide
def soko2_2Macro87M238Prefix6 : List Dir := soko2_2Macro87M238Prefix5 ++ soko2_2Macro87M238Block6
theorem soko2_2Macro87M238_prefix6_checked : run soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix6 = some ⟨soko2_2Macro87M238State224, 81, 224⟩ :=
  run_append_of soko2_2.board soko2_2.initial soko2_2Macro87M238Prefix5 soko2_2Macro87M238Block6
    ⟨soko2_2Macro87M238State192, 68, 192⟩ ⟨soko2_2Macro87M238State224, 13, 32⟩
    soko2_2Macro87M238_prefix5_checked soko2_2Macro87M238_block6_checked
end NetHack.Sokoban.Generated
