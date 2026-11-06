/- Moves-optimality from a real reachable full-map state, using only
kernel-checked tiny exact-state coverage leaves and the generic layer theorem. -/
import NetHack.Sokoban.Movement.LateCover0
import NetHack.Sokoban.Movement.LateCover1
import NetHack.Sokoban.Movement.LateCover2
import NetHack.Sokoban.Movement.LateCover3
import NetHack.Sokoban.Movement.LateCover4
import NetHack.Sokoban.Movement.LateCover5
import NetHack.Sokoban.Movement.LateCover6

namespace NetHack.Sokoban.Movement.Late
theorem layers_checked : Bounded.checkLayers soko4_2.board layers = true := by
  simp only [layers, Bounded.checkLayers,layer0_goal_free, layer1_goal_free, layer2_goal_free, layer3_goal_free, layer4_goal_free, layer5_goal_free, layer6_goal_free, layer7_goal_free, Cover0.covers, Cover1.covers, Cover2.covers, Cover3.covers, Cover4.covers, Cover5.covers, Cover6.covers, Bool.true_and]

theorem moves_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_2.board initial directions final pushes moves) (completed : Goal final) : 8 ≤ moves := by
  have bound := Bounded.layers_bound soko4_2.board layers layers_checked initial
    (by change initial ∈ [initial]; simp) directions final pushes moves trace completed
  simpa only [layers, List.length_cons, List.length_nil] using bound

theorem pushes_lower_bound {directions : List Dir} {final : State} {pushes moves : Nat}
    (trace : Trace soko4_2.board initial directions final pushes moves) (completed : Goal final) : 2 ≤ pushes := by
  have bound := Reduction.continuation_lower_bound (total := 85)
    (fun _ _ _ _ whole goal => Soko42Optimal.lower_bound whole goal) reachable trace completed
  exact bound

theorem achieved : Achievable soko4_2.board initial ⟨2,8⟩ :=
  ⟨suffix, Paths85x322.finalState, winning, Paths85x322.completed⟩

theorem both_optimal : PushesOptimal soko4_2.board initial ⟨2,8⟩ ∧
    MovesOptimal soko4_2.board initial ⟨2,8⟩ := by
  constructor
  · refine ⟨achieved, ?_⟩
    intro other winning
    rcases winning with ⟨directions, final, trace, completed⟩
    exact pushes_lower_bound trace completed
  · refine ⟨achieved, ?_⟩
    intro other winning
    rcases winning with ⟨directions, final, trace, completed⟩
    exact moves_lower_bound trace completed

theorem solvable : Solvable soko4_2.board initial := ⟨⟨2,8⟩,achieved⟩

theorem minimum_moves_exact : minimumMoves soko4_2.board initial solvable = 8 :=
  ((movesOptimal_iff_minimum solvable ⟨2,8⟩).mp both_optimal.2).2.symm

end NetHack.Sokoban.Movement.Late
