/- Statement and axiom audit for soko4-2. EXACT push minimum for this model.
Added for this package; it is not a copy from the source tree and adds no proof
content: each theorem below restates a packaged result with PushInterval unfolded.
Scope: pushes in the Model.lean profile from the canonical start; not moves, and
not a statement about full NetHack play. -/
import NetHack.Sokoban.Original42Interval85
import NetHack.Sokoban.Movement.Claims
import NetHack.Sokoban.Symmetry.Soko42AllOrientations

namespace Audit.Soko42
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Universal lower bound over every completing `Trace`. -/
theorem lower_bound : ∀ (directions : List Dir) (final : State) (pushes moves : Nat),
    Trace soko4_2.board soko4_2.initial directions final pushes moves → Goal final → 85 ≤ pushes :=
  map42.lower_bound

/-- Constructive upper bound: a completing `Trace` with exactly this push count. -/
theorem upper_bound : ∃ (directions : List Dir) (final : State) (moves : Nat),
    Trace soko4_2.board soko4_2.initial directions final 85 moves ∧ Goal final :=
  map42.upper_bound

/-- The concrete witness path, with both of its costs. -/
theorem witness : Trace soko4_2.board soko4_2.initial Generated.soko4_2CandidatePath Generated.soko4_2CandidateFinalState 85 332 ∧ Goal Generated.soko4_2CandidateFinalState :=
  ⟨Generated.soko4_2_candidate_trace, Generated.soko4_2_candidate_goal⟩

/-- The map is the one generated from the pinned upstream Lua file. -/
theorem source_pin : soko4_2.id = "soko4-2" ∧ soko4_2.sourceFile = "dat/soko4-2.lua" ∧
    soko4_2.sourceSHA256 = "70b0f36c98e8150a1e7c4771db6ab84357251a2a88b3e18c8c75ebd2e17f1e17" := ⟨rfl, rfl, rfl⟩

/-- Exact minimum: attained, and no completing trace pushes fewer times. -/
theorem exact_minimum :
    (∃ (directions : List Dir) (final : State) (moves : Nat),
      Trace soko4_2.board soko4_2.initial directions final 85 moves ∧ Goal final) ∧
    (∀ (directions : List Dir) (final : State) (pushes moves : Nat),
      Trace soko4_2.board soko4_2.initial directions final pushes moves → Goal final → 85 ≤ pushes) :=
  ⟨upper_bound, lower_bound⟩

end Audit.Soko42

#print NetHack.Sokoban.Goal
#print NetHack.Sokoban.Trace
#print NetHack.Sokoban.InitialIntervals.PushInterval
#check @Audit.Soko42.lower_bound
#check @Audit.Soko42.upper_bound
#check @Audit.Soko42.witness
#check @Audit.Soko42.source_pin
#check @Audit.Soko42.exact_minimum
#check @NetHack.Sokoban.InitialIntervals.map42
#check @NetHack.Sokoban.Soko42Optimal.lower_bound
#check @NetHack.Sokoban.Generated.soko4_2_candidate_trace
#check @NetHack.Sokoban.Generated.soko4_2_candidate_goal
#check @NetHack.Sokoban.Soko42Optimal.optimal
#check @NetHack.Sokoban.Movement.Claims.pushes_optimal85x322
#check @NetHack.Sokoban.Symmetry.Soko42AllOrientations.optimal
#print axioms Audit.Soko42.lower_bound
#print axioms Audit.Soko42.upper_bound
#print axioms Audit.Soko42.witness
#print axioms Audit.Soko42.source_pin
#print axioms Audit.Soko42.exact_minimum
#print axioms NetHack.Sokoban.InitialIntervals.map42
#print axioms NetHack.Sokoban.Soko42Optimal.lower_bound
#print axioms NetHack.Sokoban.Generated.soko4_2_candidate_trace
#print axioms NetHack.Sokoban.Generated.soko4_2_candidate_goal
#print axioms NetHack.Sokoban.Soko42Optimal.optimal
#print axioms NetHack.Sokoban.Movement.Claims.pushes_optimal85x322
#print axioms NetHack.Sokoban.Symmetry.Soko42AllOrientations.optimal
