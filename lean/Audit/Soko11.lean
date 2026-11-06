/- Statement and axiom audit for soko1-1. INTERVAL: the exact minimum is an open mathematical question.
Added for this package; it is not a copy from the source tree and adds no proof
content: each theorem below restates a packaged result with PushInterval unfolded.
Scope: pushes in the Model.lean profile from the canonical start; not moves, and
not a statement about full NetHack play. -/
import NetHack.Sokoban.Original11Interval321

namespace Audit.Soko11
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Universal lower bound over every completing `Trace`. -/
theorem lower_bound : ∀ (directions : List Dir) (final : State) (pushes moves : Nat),
    Trace soko1_1.board soko1_1.initial directions final pushes moves → Goal final → 321 ≤ pushes :=
  map11.lower_bound

/-- Constructive upper bound: a completing `Trace` with exactly this push count. -/
theorem upper_bound : ∃ (directions : List Dir) (final : State) (moves : Nat),
    Trace soko1_1.board soko1_1.initial directions final 375 moves ∧ Goal final :=
  map11.upper_bound

/-- The concrete witness path, with both of its costs. -/
theorem witness : Trace soko1_1.board soko1_1.initial Generated.soko1_1Macro375M778Path Generated.soko1_1Macro375M778FinalState 375 778 ∧ Goal Generated.soko1_1Macro375M778FinalState :=
  Generated.soko1_1_macro375_m778_solution

/-- The map is the one generated from the pinned upstream Lua file. -/
theorem source_pin : soko1_1.id = "soko1-1" ∧ soko1_1.sourceFile = "dat/soko1-1.lua" ∧
    soko1_1.sourceSHA256 = "b6197437573a59c1301e423cde20c49884ae9fcce478a02f4ea8e806f517a4ff" := ⟨rfl, rfl, rfl⟩

end Audit.Soko11

#print NetHack.Sokoban.Goal
#print NetHack.Sokoban.Trace
#print NetHack.Sokoban.InitialIntervals.PushInterval
#check @Audit.Soko11.lower_bound
#check @Audit.Soko11.upper_bound
#check @Audit.Soko11.witness
#check @Audit.Soko11.source_pin
#check @NetHack.Sokoban.InitialIntervals.map11
#check @NetHack.Soko11PairCandidate321.pushes_lower_bound
#check @NetHack.Sokoban.Generated.soko1_1_macro375_m778_solution
#print axioms Audit.Soko11.lower_bound
#print axioms Audit.Soko11.upper_bound
#print axioms Audit.Soko11.witness
#print axioms Audit.Soko11.source_pin
#print axioms NetHack.Sokoban.InitialIntervals.map11
#print axioms NetHack.Soko11PairCandidate321.pushes_lower_bound
#print axioms NetHack.Sokoban.Generated.soko1_1_macro375_m778_solution
