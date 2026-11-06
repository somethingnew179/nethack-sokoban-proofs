/- Statement and axiom audit for soko2-2. EXACT push minimum for this model.
Added for this package; it is not a copy from the source tree and adds no proof
content: each theorem below restates a packaged result with PushInterval unfolded.
Scope: pushes in the Model.lean profile from the canonical start; not moves, and
not a statement about full NetHack play. -/
import NetHack.Sokoban.Original22Interval87

namespace Audit.Soko22
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Universal lower bound over every completing `Trace`. -/
theorem lower_bound : ∀ (directions : List Dir) (final : State) (pushes moves : Nat),
    Trace soko2_2.board soko2_2.initial directions final pushes moves → Goal final → 87 ≤ pushes :=
  map22.lower_bound

/-- Constructive upper bound: a completing `Trace` with exactly this push count. -/
theorem upper_bound : ∃ (directions : List Dir) (final : State) (moves : Nat),
    Trace soko2_2.board soko2_2.initial directions final 87 moves ∧ Goal final :=
  map22.upper_bound

/-- The concrete witness path, with both of its costs. -/
theorem witness : Trace soko2_2.board soko2_2.initial Generated.soko2_2Macro87M238Path Generated.soko2_2Macro87M238FinalState 87 238 ∧ Goal Generated.soko2_2Macro87M238FinalState :=
  Generated.soko2_2_macro87_m238_solution

/-- The map is the one generated from the pinned upstream Lua file. -/
theorem source_pin : soko2_2.id = "soko2-2" ∧ soko2_2.sourceFile = "dat/soko2-2.lua" ∧
    soko2_2.sourceSHA256 = "2d20b75e8186d24a954cc398897622b10b59789e9b96f0ce52f462b6364e327b" := ⟨rfl, rfl, rfl⟩

/-- Exact minimum: attained, and no completing trace pushes fewer times. -/
theorem exact_minimum :
    (∃ (directions : List Dir) (final : State) (moves : Nat),
      Trace soko2_2.board soko2_2.initial directions final 87 moves ∧ Goal final) ∧
    (∀ (directions : List Dir) (final : State) (pushes moves : Nat),
      Trace soko2_2.board soko2_2.initial directions final pushes moves → Goal final → 87 ≤ pushes) :=
  ⟨upper_bound, lower_bound⟩

end Audit.Soko22

#print NetHack.Sokoban.Goal
#print NetHack.Sokoban.Trace
#print NetHack.Sokoban.InitialIntervals.PushInterval
#check @Audit.Soko22.lower_bound
#check @Audit.Soko22.upper_bound
#check @Audit.Soko22.witness
#check @Audit.Soko22.source_pin
#check @Audit.Soko22.exact_minimum
#check @NetHack.Sokoban.InitialIntervals.map22
#check @NetHack.Soko22Hazard87.pushes_lower_bound
#check @NetHack.Sokoban.Generated.soko2_2_macro87_m238_solution
#check @NetHack.Soko22Hazard87.minimum87
#print axioms Audit.Soko22.lower_bound
#print axioms Audit.Soko22.upper_bound
#print axioms Audit.Soko22.witness
#print axioms Audit.Soko22.source_pin
#print axioms Audit.Soko22.exact_minimum
#print axioms NetHack.Sokoban.InitialIntervals.map22
#print axioms NetHack.Soko22Hazard87.pushes_lower_bound
#print axioms NetHack.Sokoban.Generated.soko2_2_macro87_m238_solution
#print axioms NetHack.Soko22Hazard87.minimum87
