/- Statement and axiom audit for soko3-1. EXACT push minimum for this model.
Added for this package; it is not a copy from the source tree and adds no proof
content: each theorem below restates a packaged result with PushInterval unfolded.
Scope: pushes in the Model.lean profile from the canonical start; not moves, and
not a statement about full NetHack play. -/
import NetHack.Sokoban.Original31Interval136

namespace Audit.Soko31
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Universal lower bound over every completing `Trace`. -/
theorem lower_bound : ∀ (directions : List Dir) (final : State) (pushes moves : Nat),
    Trace soko3_1.board soko3_1.initial directions final pushes moves → Goal final → 136 ≤ pushes :=
  map31.lower_bound

/-- Constructive upper bound: a completing `Trace` with exactly this push count. -/
theorem upper_bound : ∃ (directions : List Dir) (final : State) (moves : Nat),
    Trace soko3_1.board soko3_1.initial directions final 136 moves ∧ Goal final :=
  map31.upper_bound

/-- The concrete witness path, with both of its costs. -/
theorem witness : Trace soko3_1.board soko3_1.initial Generated.soko3_1Macro136M270Path Generated.soko3_1Macro136M270FinalState 136 270 ∧ Goal Generated.soko3_1Macro136M270FinalState :=
  Generated.soko3_1_macro136_m270_solution

/-- The map is the one generated from the pinned upstream Lua file. -/
theorem source_pin : soko3_1.id = "soko3-1" ∧ soko3_1.sourceFile = "dat/soko3-1.lua" ∧
    soko3_1.sourceSHA256 = "1be490e328d552115f6e3907fb7d656835e18daf7183942ae26ef6a4d58c271a" := ⟨rfl, rfl, rfl⟩

/-- Exact minimum: attained, and no completing trace pushes fewer times. -/
theorem exact_minimum :
    (∃ (directions : List Dir) (final : State) (moves : Nat),
      Trace soko3_1.board soko3_1.initial directions final 136 moves ∧ Goal final) ∧
    (∀ (directions : List Dir) (final : State) (pushes moves : Nat),
      Trace soko3_1.board soko3_1.initial directions final pushes moves → Goal final → 136 ≤ pushes) :=
  ⟨upper_bound, lower_bound⟩

end Audit.Soko31

#print NetHack.Sokoban.Goal
#print NetHack.Sokoban.Trace
#print NetHack.Sokoban.InitialIntervals.PushInterval
#check @Audit.Soko31.lower_bound
#check @Audit.Soko31.upper_bound
#check @Audit.Soko31.witness
#check @Audit.Soko31.source_pin
#check @Audit.Soko31.exact_minimum
#check @NetHack.Sokoban.InitialIntervals.map31
#check @NetHack.Soko31Optimal136.pushes_lower_bound
#check @NetHack.Sokoban.Generated.soko3_1_macro136_m270_solution
#check @NetHack.Soko31Optimal136.minimum136
#print axioms Audit.Soko31.lower_bound
#print axioms Audit.Soko31.upper_bound
#print axioms Audit.Soko31.witness
#print axioms Audit.Soko31.source_pin
#print axioms Audit.Soko31.exact_minimum
#print axioms NetHack.Sokoban.InitialIntervals.map31
#print axioms NetHack.Soko31Optimal136.pushes_lower_bound
#print axioms NetHack.Sokoban.Generated.soko3_1_macro136_m270_solution
#print axioms NetHack.Soko31Optimal136.minimum136
