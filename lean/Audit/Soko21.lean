/- Statement and axiom audit for soko2-1. EXACT push minimum for this model.
Added for this package; it is not a copy from the source tree and adds no proof
content: each theorem below restates a packaged result with PushInterval unfolded.
Scope: pushes in the Model.lean profile from the canonical start; not moves, and
not a statement about full NetHack play. -/
import NetHack.Sokoban.Original21Interval109

namespace Audit.Soko21
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Universal lower bound over every completing `Trace`. -/
theorem lower_bound : ∀ (directions : List Dir) (final : State) (pushes moves : Nat),
    Trace soko2_1.board soko2_1.initial directions final pushes moves → Goal final → 109 ≤ pushes :=
  map21.lower_bound

/-- Constructive upper bound: a completing `Trace` with exactly this push count. -/
theorem upper_bound : ∃ (directions : List Dir) (final : State) (moves : Nat),
    Trace soko2_1.board soko2_1.initial directions final 109 moves ∧ Goal final :=
  map21.upper_bound

/-- The concrete witness path, with both of its costs. -/
theorem witness : Trace soko2_1.board soko2_1.initial Generated.soko2_1CandidatePath Generated.soko2_1CandidateFinalState 109 475 ∧ Goal Generated.soko2_1CandidateFinalState :=
  ⟨Generated.soko2_1_candidate_trace, Generated.soko2_1_candidate_goal⟩

/-- The map is the one generated from the pinned upstream Lua file. -/
theorem source_pin : soko2_1.id = "soko2-1" ∧ soko2_1.sourceFile = "dat/soko2-1.lua" ∧
    soko2_1.sourceSHA256 = "7513e1882b1a70c6cf4317a559584ca5826b2815875d21d0865bb4e5501c297b" := ⟨rfl, rfl, rfl⟩

/-- Exact minimum: attained, and no completing trace pushes fewer times. -/
theorem exact_minimum :
    (∃ (directions : List Dir) (final : State) (moves : Nat),
      Trace soko2_1.board soko2_1.initial directions final 109 moves ∧ Goal final) ∧
    (∀ (directions : List Dir) (final : State) (pushes moves : Nat),
      Trace soko2_1.board soko2_1.initial directions final pushes moves → Goal final → 109 ≤ pushes) :=
  ⟨upper_bound, lower_bound⟩

end Audit.Soko21

#print NetHack.Sokoban.Goal
#print NetHack.Sokoban.Trace
#print NetHack.Sokoban.InitialIntervals.PushInterval
#check @Audit.Soko21.lower_bound
#check @Audit.Soko21.upper_bound
#check @Audit.Soko21.witness
#check @Audit.Soko21.source_pin
#check @Audit.Soko21.exact_minimum
#check @NetHack.Sokoban.InitialIntervals.map21
#check @NetHack.Sokoban21.soko2_1_pushes_lower_bound
#check @NetHack.Sokoban.Generated.soko2_1_candidate_trace
#check @NetHack.Sokoban.Generated.soko2_1_candidate_goal
#check @NetHack.Sokoban21.soko2_1_pushes_optimal
#print axioms Audit.Soko21.lower_bound
#print axioms Audit.Soko21.upper_bound
#print axioms Audit.Soko21.witness
#print axioms Audit.Soko21.source_pin
#print axioms Audit.Soko21.exact_minimum
#print axioms NetHack.Sokoban.InitialIntervals.map21
#print axioms NetHack.Sokoban21.soko2_1_pushes_lower_bound
#print axioms NetHack.Sokoban.Generated.soko2_1_candidate_trace
#print axioms NetHack.Sokoban.Generated.soko2_1_candidate_goal
#print axioms NetHack.Sokoban21.soko2_1_pushes_optimal
