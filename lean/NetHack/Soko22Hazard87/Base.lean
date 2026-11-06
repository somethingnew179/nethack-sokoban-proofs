/- Untrusted proposed candidate; every stated lemma uses the Lean kernel. -/
import NetHack.Sokoban.HazardCorrection
import NetHack.Sokoban.ClosedComponents
import NetHack.Sokoban22Refined85.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem range_ite (test : Bool) (a b : Int) (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2) :
    0 ≤ (if test then a else b) ∧ (if test then a else b) ≤ 2 := by cases h : test <;> simp only [h, Bool.false_eq_true, ↓reduceIte] <;> assumption
end NetHack.Soko22Hazard87
