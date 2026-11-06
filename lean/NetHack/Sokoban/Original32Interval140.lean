/- Full original3-2 interval140..147, same profile, same Trace147/764. -/
import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Soko32Disjoint.Verified140
import NetHack.Sokoban.Generated.Soko32Macro147M764Solution
namespace NetHack.Sokoban.InitialIntervals
open Generated
theorem map32_140 : PushInterval soko3_2 140 147 :=
  ⟨fun _ _ _ _ trace completed => NetHack.Soko32Disjoint.pushes_lower_bound trace completed,
    ⟨soko3_2Macro147M764Path,soko3_2Macro147M764FinalState,764,
      soko3_2_macro147_m764_trace,soko3_2_macro147_m764_goal⟩⟩
end NetHack.Sokoban.InitialIntervals
