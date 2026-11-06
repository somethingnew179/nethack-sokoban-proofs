/- Closed movement facts for the real soko4-2 map, under Model's profile.
A pair of incomparable witnesses is not a proof of a Pareto frontier, and
an upper bound319 is not a proof of a minimum319. -/
import NetHack.Sokoban.Movement.Paths85x322
import NetHack.Sokoban.Movement.Paths92x319
import NetHack.Sokoban.Movement.Late

namespace NetHack.Sokoban.Movement.Claims

theorem achieved85x322 : Achievable soko4_2.board soko4_2.initial ⟨85,322⟩ :=
  ⟨Paths85x322.path, Paths85x322.finalState, Paths85x322.trace, Paths85x322.completed⟩

theorem achieved92x319 : Achievable soko4_2.board soko4_2.initial ⟨92,319⟩ :=
  ⟨Paths92x319.path, Paths92x319.finalState, Paths92x319.trace, Paths92x319.completed⟩

theorem achieved85x332 : Achievable soko4_2.board soko4_2.initial ⟨85,332⟩ :=
  ⟨Generated.soko4_2CandidatePath, Generated.soko4_2CandidateFinalState,
    Generated.soko4_2_candidate_trace, Generated.soko4_2_candidate_goal⟩

theorem incomparable_witnesses : Incomparable ⟨85,322⟩ ⟨92,319⟩ := by
  unfold Incomparable ComponentwiseLe
  decide

theorem old_cost_dominated : StrictlyDominates ⟨85,322⟩ ⟨85,332⟩ := by
  unfold StrictlyDominates ComponentwiseLe
  decide

theorem pushes_optimal85x322 : PushesOptimal soko4_2.board soko4_2.initial ⟨85,322⟩ := by
  refine ⟨achieved85x322, ?_⟩
  intro other winning
  rcases winning with ⟨directions, final, trace, completed⟩
  exact Soko42Optimal.lower_bound trace completed

theorem pushes_optimal85x332 : PushesOptimal soko4_2.board soko4_2.initial ⟨85,332⟩ := by
  refine ⟨achieved85x332, ?_⟩
  intro other winning
  rcases winning with ⟨directions, final, trace, completed⟩
  exact Soko42Optimal.lower_bound trace completed

theorem not_moves_optimal85x322 : ¬ MovesOptimal soko4_2.board soko4_2.initial ⟨85,322⟩ := by
  intro alleged
  have impossible := alleged.2 ⟨92,319⟩ achieved92x319
  change 322 ≤ 319 at impossible
  omega

theorem not_pushes_optimal92x319 : ¬ PushesOptimal soko4_2.board soko4_2.initial ⟨92,319⟩ := by
  intro alleged
  have impossible := alleged.2 ⟨85,322⟩ achieved85x322
  change 92 ≤ 85 at impossible
  omega

theorem not_moves_optimal85x332 : ¬ MovesOptimal soko4_2.board soko4_2.initial ⟨85,332⟩ := by
  intro alleged
  have impossible := alleged.2 ⟨85,322⟩ achieved85x322
  change 332 ≤ 322 at impossible
  omega

theorem not_pushLex_optimal85x332 : ¬ PushLexOptimal soko4_2.board soko4_2.initial ⟨85,332⟩ := by
  intro alleged
  have impossible := alleged.2 ⟨85,322⟩ achieved85x322
  change (85 < 85 ∨ (85 = 85 ∧ 332 ≤ 322)) at impossible
  omega

theorem not_moveLex_optimal85x322 : ¬ MoveLexOptimal soko4_2.board soko4_2.initial ⟨85,322⟩ := by
  intro alleged
  exact not_moves_optimal85x322 ((moveLex_iff _ _ _).mp alleged).1

theorem not_pareto_optimal85x332 : ¬ ParetoOptimal soko4_2.board soko4_2.initial ⟨85,332⟩ := by
  intro alleged
  exact alleged.2 ⟨85,322⟩ achieved85x322 old_cost_dominated

theorem pushes_minimum_does_not_imply_lex_or_pareto :
    PushesOptimal soko4_2.board soko4_2.initial ⟨85,332⟩ ∧
    ¬ PushLexOptimal soko4_2.board soko4_2.initial ⟨85,332⟩ ∧
    ¬ ParetoOptimal soko4_2.board soko4_2.initial ⟨85,332⟩ :=
  ⟨pushes_optimal85x332, not_pushLex_optimal85x332, not_pareto_optimal85x332⟩

theorem solvable : Solvable soko4_2.board soko4_2.initial := ⟨⟨92,319⟩,achieved92x319⟩

/-- Global movement interval; neither endpoint is asserted attained as a
moves minimum. In particular, this is not minimumMoves=319. -/
theorem initial_minimum_moves_bounds :
    85 ≤ minimumMoves soko4_2.board soko4_2.initial solvable ∧
      minimumMoves soko4_2.board soko4_2.initial solvable ≤ 319 := by
  constructor
  · apply (minimumMoves_lower_iff solvable 85).mpr
    intro cost achieved
    rcases achieved with ⟨directions, final, trace, completed⟩
    have pushes := Soko42Optimal.lower_bound trace completed
    have moves := LowerBounds.trace_pushes_le_moves trace
    omega
  · exact minimumMoves_le solvable ⟨92,319⟩ achieved92x319

end NetHack.Sokoban.Movement.Claims
