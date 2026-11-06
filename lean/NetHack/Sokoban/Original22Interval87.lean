import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Soko22Hazard87.LowerBound
import NetHack.Soko22Witness87.Soko22Macro87M238Solution
namespace NetHack.Sokoban.InitialIntervals
open Generated
theorem map22 : PushInterval soko2_2 87 87 :=
  ⟨fun _ _ _ _ trace completed => NetHack.Soko22Hazard87.pushes_lower_bound trace completed,
    ⟨soko2_2Macro87M238Path,soko2_2Macro87M238FinalState,238,soko2_2_macro87_m238_trace,soko2_2_macro87_m238_goal⟩⟩
end NetHack.Sokoban.InitialIntervals
