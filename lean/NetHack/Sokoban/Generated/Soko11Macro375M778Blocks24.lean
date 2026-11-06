/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko11Macro375M778Blocks23
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_1Macro375M778Block24 : List Dir := [.north, .north, .northEast, .west, .southWest, .north, .north, .north, .northWest, .east]
def soko1_1Macro375M778State778 : State := {player := 33, boulders := [315, 321], holes := []}
theorem soko1_1Macro375M778_block24_checked : run soko1_1.board soko1_1Macro375M778State768 soko1_1Macro375M778Block24 = some ⟨soko1_1Macro375M778State778, 7, 10⟩ := by decide
def soko1_1Macro375M778Prefix24 : List Dir := soko1_1Macro375M778Prefix23 ++ soko1_1Macro375M778Block24
theorem soko1_1Macro375M778_prefix24_checked : run soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix24 = some ⟨soko1_1Macro375M778State778, 375, 778⟩ :=
  run_append_of soko1_1.board soko1_1.initial soko1_1Macro375M778Prefix23 soko1_1Macro375M778Block24
    ⟨soko1_1Macro375M778State768, 368, 768⟩ ⟨soko1_1Macro375M778State778, 7, 10⟩
    soko1_1Macro375M778_prefix23_checked soko1_1Macro375M778_block24_checked
end NetHack.Sokoban.Generated
