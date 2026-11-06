import NetHack.Sokoban.InitialIntervalTypes
import NetHack.Sokoban41.Soko41Optimal
namespace NetHack.Sokoban.InitialIntervals
open Generated
theorem map41 : PushInterval soko4_1 80 80 :=
  ⟨fun _ _ _ _ trace completed => NetHack.Sokoban41.soko4_1_pushes_lower_bound trace completed,
    ⟨soko4_1CandidatePath,soko4_1CandidateFinalState,299,soko4_1_candidate_trace,soko4_1_candidate_goal⟩⟩
end NetHack.Sokoban.InitialIntervals
