import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Soko11PairCandidate321.Verified
import NetHack.Sokoban.Generated.Soko11Macro375M778Solution
namespace NetHack.Sokoban.InitialIntervals
open Generated
theorem map11 : PushInterval soko1_1 321 375 :=
  ⟨fun _ _ _ _ trace completed => NetHack.Soko11PairCandidate321.pushes_lower_bound trace completed,
    ⟨soko1_1Macro375M778Path, soko1_1Macro375M778FinalState,778,soko1_1_macro375_m778_trace,soko1_1_macro375_m778_goal⟩⟩
end NetHack.Sokoban.InitialIntervals
