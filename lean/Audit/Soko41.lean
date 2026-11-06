/- Statement and axiom audit for soko4-1. EXACT push minimum for this model.
Added for this package; it is not a copy from the source tree and adds no proof
content: each theorem below restates a packaged result with PushInterval unfolded.
Scope: pushes in the Model.lean profile from the canonical start; not moves, and
not a statement about full NetHack play. -/
import NetHack.Sokoban.Original41Interval80

namespace Audit.Soko41
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Universal lower bound over every completing `Trace`. -/
theorem lower_bound : ∀ (directions : List Dir) (final : State) (pushes moves : Nat),
    Trace soko4_1.board soko4_1.initial directions final pushes moves → Goal final → 80 ≤ pushes :=
  map41.lower_bound

/-- Constructive upper bound: a completing `Trace` with exactly this push count. -/
theorem upper_bound : ∃ (directions : List Dir) (final : State) (moves : Nat),
    Trace soko4_1.board soko4_1.initial directions final 80 moves ∧ Goal final :=
  map41.upper_bound

/-- The concrete witness path, with both of its costs. -/
theorem witness : Trace soko4_1.board soko4_1.initial Generated.soko4_1CandidatePath Generated.soko4_1CandidateFinalState 80 299 ∧ Goal Generated.soko4_1CandidateFinalState :=
  ⟨Generated.soko4_1_candidate_trace, Generated.soko4_1_candidate_goal⟩

/-- The map is the one generated from the pinned upstream Lua file. -/
theorem source_pin : soko4_1.id = "soko4-1" ∧ soko4_1.sourceFile = "dat/soko4-1.lua" ∧
    soko4_1.sourceSHA256 = "d7047eb1a4c7d06e4f38d976105a9c026e334206ce3b9d5fedf9fcc75e1bb1df" := ⟨rfl, rfl, rfl⟩

/-- Exact minimum: attained, and no completing trace pushes fewer times. -/
theorem exact_minimum :
    (∃ (directions : List Dir) (final : State) (moves : Nat),
      Trace soko4_1.board soko4_1.initial directions final 80 moves ∧ Goal final) ∧
    (∀ (directions : List Dir) (final : State) (pushes moves : Nat),
      Trace soko4_1.board soko4_1.initial directions final pushes moves → Goal final → 80 ≤ pushes) :=
  ⟨upper_bound, lower_bound⟩

end Audit.Soko41

#print NetHack.Sokoban.Goal
#print NetHack.Sokoban.Trace
#print NetHack.Sokoban.InitialIntervals.PushInterval
#check @Audit.Soko41.lower_bound
#check @Audit.Soko41.upper_bound
#check @Audit.Soko41.witness
#check @Audit.Soko41.source_pin
#check @Audit.Soko41.exact_minimum
#check @NetHack.Sokoban.InitialIntervals.map41
#check @NetHack.Sokoban41.soko4_1_pushes_lower_bound
#check @NetHack.Sokoban.Generated.soko4_1_candidate_trace
#check @NetHack.Sokoban.Generated.soko4_1_candidate_goal
#check @NetHack.Sokoban41.soko4_1_pushes_optimal
#print axioms Audit.Soko41.lower_bound
#print axioms Audit.Soko41.upper_bound
#print axioms Audit.Soko41.witness
#print axioms Audit.Soko41.source_pin
#print axioms Audit.Soko41.exact_minimum
#print axioms NetHack.Sokoban.InitialIntervals.map41
#print axioms NetHack.Sokoban41.soko4_1_pushes_lower_bound
#print axioms NetHack.Sokoban.Generated.soko4_1_candidate_trace
#print axioms NetHack.Sokoban.Generated.soko4_1_candidate_goal
#print axioms NetHack.Sokoban41.soko4_1_pushes_optimal
