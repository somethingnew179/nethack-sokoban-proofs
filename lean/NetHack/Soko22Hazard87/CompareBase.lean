import NetHack.Soko22Hazard87.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem integer_range_ite (test : Bool) (a b la ua lb ub : Int)
    (ha : la ≤ a ∧ a ≤ ua) (hb : lb ≤ b ∧ b ≤ ub) :
    min la lb ≤ (if test then a else b) ∧ (if test then a else b) ≤ max ua ub := by
  cases selected : test <;> simp only [selected, Bool.false_eq_true, ↓reduceIte]
  · exact ⟨Int.le_trans (Int.min_le_right _ _) hb.1, Int.le_trans hb.2 (Int.le_max_right _ _)⟩
  · exact ⟨Int.le_trans (Int.min_le_left _ _) ha.1, Int.le_trans ha.2 (Int.le_max_left _ _)⟩
end NetHack.Soko22Hazard87
