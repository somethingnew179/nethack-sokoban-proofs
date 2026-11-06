/- Full canonical map witness; ordinary kernel checks. No minimality claim. -/
import NetHack.Sokoban.Generated.Soko12Macro235M578Blocks17
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace NetHack.Sokoban.Generated
def soko1_2Macro235M578Block18 : List Dir := [.northWest, .east]
def soko1_2Macro235M578State578 : State := {player := 30, boulders := [168, 142], holes := []}
theorem soko1_2Macro235M578_block18_checked : run soko1_2.board soko1_2Macro235M578State576 soko1_2Macro235M578Block18 = some ⟨soko1_2Macro235M578State578, 1, 2⟩ := by decide +kernel
def soko1_2Macro235M578Prefix18 : List Dir := soko1_2Macro235M578Prefix17 ++ soko1_2Macro235M578Block18
theorem soko1_2Macro235M578_prefix18_checked : run soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix18 = some ⟨soko1_2Macro235M578State578, 235, 578⟩ :=
  run_append_of soko1_2.board soko1_2.initial soko1_2Macro235M578Prefix17 soko1_2Macro235M578Block18
    ⟨soko1_2Macro235M578State576, 234, 576⟩ ⟨soko1_2Macro235M578State578, 1, 2⟩
    soko1_2Macro235M578_prefix17_checked soko1_2Macro235M578_block18_checked
end NetHack.Sokoban.Generated
