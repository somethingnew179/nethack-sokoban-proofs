import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Sokoban21.Soko21Optimal
namespace NetHack.Sokoban.InitialIntervals
open Generated
theorem map21 : PushInterval soko2_1 109 109 :=
  ⟨fun _ _ _ _ trace completed => NetHack.Sokoban21.soko2_1_pushes_lower_bound trace completed,
    ⟨soko2_1CandidatePath,soko2_1CandidateFinalState,475,soko2_1_candidate_trace,soko2_1_candidate_goal⟩⟩
end NetHack.Sokoban.InitialIntervals
