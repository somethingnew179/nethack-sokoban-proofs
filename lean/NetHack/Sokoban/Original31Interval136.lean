import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Soko31Optimal136.Verified
namespace NetHack.Sokoban.InitialIntervals
open Generated
theorem map31 : PushInterval soko3_1 136 136 :=
  ⟨fun _ _ _ _ trace completed => NetHack.Soko31Optimal136.pushes_lower_bound trace completed,
    ⟨soko3_1Macro136M270Path,soko3_1Macro136M270FinalState,270,soko3_1_macro136_m270_trace,soko3_1_macro136_m270_goal⟩⟩
end NetHack.Sokoban.InitialIntervals
