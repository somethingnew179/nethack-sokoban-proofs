import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Sokoban.Soko42Optimal
namespace NetHack.Sokoban.InitialIntervals
open Generated
theorem map42 : PushInterval soko4_2 85 85 :=
  ⟨fun _ _ _ _ trace completed => Soko42Optimal.lower_bound trace completed,
    ⟨soko4_2CandidatePath,soko4_2CandidateFinalState,332,
      soko4_2_candidate_trace,soko4_2_candidate_goal⟩⟩

end NetHack.Sokoban.InitialIntervals
