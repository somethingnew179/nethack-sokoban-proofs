/- Statement and axiom audit for soko3-2. INTERVAL: the exact minimum is an open mathematical question.
Added for this package; it is not a copy from the source tree and adds no proof
content: each theorem below restates a packaged result with PushInterval unfolded.
Scope: pushes in the Model.lean profile from the canonical start; not moves, and
not a statement about full NetHack play. -/
import NetHack.Sokoban.Original32Interval140

namespace Audit.Soko32
open NetHack.Sokoban NetHack.Sokoban.InitialIntervals

/-- Universal lower bound over every completing `Trace`. -/
theorem lower_bound : ∀ (directions : List Dir) (final : State) (pushes moves : Nat),
    Trace soko3_2.board soko3_2.initial directions final pushes moves → Goal final → 140 ≤ pushes :=
  map32_140.lower_bound

/-- Constructive upper bound: a completing `Trace` with exactly this push count. -/
theorem upper_bound : ∃ (directions : List Dir) (final : State) (moves : Nat),
    Trace soko3_2.board soko3_2.initial directions final 147 moves ∧ Goal final :=
  map32_140.upper_bound

/-- The concrete witness path, with both of its costs. -/
theorem witness : Trace soko3_2.board soko3_2.initial Generated.soko3_2Macro147M764Path Generated.soko3_2Macro147M764FinalState 147 764 ∧ Goal Generated.soko3_2Macro147M764FinalState :=
  Generated.soko3_2_macro147_m764_solution

/-- The map is the one generated from the pinned upstream Lua file. -/
theorem source_pin : soko3_2.id = "soko3-2" ∧ soko3_2.sourceFile = "dat/soko3-2.lua" ∧
    soko3_2.sourceSHA256 = "d6d810b284cb7ba41c2ce5c3d16521010c88d89bca0ac0e64365824c7e114cd7" := ⟨rfl, rfl, rfl⟩

end Audit.Soko32

#print NetHack.Sokoban.Goal
#print NetHack.Sokoban.Trace
#print NetHack.Sokoban.InitialIntervals.PushInterval
#check @Audit.Soko32.lower_bound
#check @Audit.Soko32.upper_bound
#check @Audit.Soko32.witness
#check @Audit.Soko32.source_pin
#check @NetHack.Sokoban.InitialIntervals.map32_140
#check @NetHack.Soko32Disjoint.pushes_lower_bound
#check @NetHack.Sokoban.Generated.soko3_2_macro147_m764_solution
#print axioms Audit.Soko32.lower_bound
#print axioms Audit.Soko32.upper_bound
#print axioms Audit.Soko32.witness
#print axioms Audit.Soko32.source_pin
#print axioms NetHack.Sokoban.InitialIntervals.map32_140
#print axioms NetHack.Soko32Disjoint.pushes_lower_bound
#print axioms NetHack.Sokoban.Generated.soko3_2_macro147_m764_solution
