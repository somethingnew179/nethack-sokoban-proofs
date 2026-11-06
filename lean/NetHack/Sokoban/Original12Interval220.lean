import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Soko12Forward220.Unified.Verified220
import NetHack.Sokoban.Generated.Soko12Macro235M578Solution
namespace NetHack.Sokoban.InitialIntervals
open Generated
theorem map12 : PushInterval soko1_2 220 235 :=
  ⟨fun _ _ _ _ trace completed => NetHack.Soko12Forward220.Unified.Verified220.pushes_lower_bound trace completed,
    ⟨soko1_2Macro235M578Path, soko1_2Macro235M578FinalState,578,soko1_2_macro235_m578_trace,soko1_2_macro235_m578_goal⟩⟩
end NetHack.Sokoban.InitialIntervals
