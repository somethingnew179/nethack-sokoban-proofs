/- Statement and axiom audit for soko1-2. INTERVAL: the exact minimum is an open mathematical question.
Added for this package; it is not a copy from the source tree and adds no proof
content: each theorem below restates a packaged result with PushInterval unfolded.
Scope: pushes in the Model.lean profile from the canonical start; not moves, and
not a statement about full NetHack play. -/
import NetHack.Sokoban.Original12Interval220

namespace Audit.Soko12
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Universal lower bound over every completing `Trace`. -/
theorem lower_bound : ∀ (directions : List Dir) (final : State) (pushes moves : Nat),
    Trace soko1_2.board soko1_2.initial directions final pushes moves → Goal final → 220 ≤ pushes :=
  map12.lower_bound

/-- Constructive upper bound: a completing `Trace` with exactly this push count. -/
theorem upper_bound : ∃ (directions : List Dir) (final : State) (moves : Nat),
    Trace soko1_2.board soko1_2.initial directions final 235 moves ∧ Goal final :=
  map12.upper_bound

/-- The concrete witness path, with both of its costs. -/
theorem witness : Trace soko1_2.board soko1_2.initial Generated.soko1_2Macro235M578Path Generated.soko1_2Macro235M578FinalState 235 578 ∧ Goal Generated.soko1_2Macro235M578FinalState :=
  Generated.soko1_2_macro235_m578_solution

/-- The map is the one generated from the pinned upstream Lua file. -/
theorem source_pin : soko1_2.id = "soko1-2" ∧ soko1_2.sourceFile = "dat/soko1-2.lua" ∧
    soko1_2.sourceSHA256 = "0fcdc3d01c24c8277e06d83b8cfd0aa3409ac8a4531e11d6bfeba7166938f561" := ⟨rfl, rfl, rfl⟩

end Audit.Soko12

#print NetHack.Sokoban.Goal
#print NetHack.Sokoban.Trace
#print NetHack.Sokoban.InitialIntervals.PushInterval
#check @Audit.Soko12.lower_bound
#check @Audit.Soko12.upper_bound
#check @Audit.Soko12.witness
#check @Audit.Soko12.source_pin
#check @NetHack.Sokoban.InitialIntervals.map12
#check @NetHack.Soko12Forward220.Unified.Verified220.pushes_lower_bound
#check @NetHack.Sokoban.Generated.soko1_2_macro235_m578_solution
#print axioms Audit.Soko12.lower_bound
#print axioms Audit.Soko12.upper_bound
#print axioms Audit.Soko12.witness
#print axioms Audit.Soko12.source_pin
#print axioms NetHack.Sokoban.InitialIntervals.map12
#print axioms NetHack.Soko12Forward220.Unified.Verified220.pushes_lower_bound
#print axioms NetHack.Sokoban.Generated.soko1_2_macro235_m578_solution
