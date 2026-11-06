/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GoalSemantic03
import NetHack.Sokoban41.GoalComparisons02
set_option maxRecDepth 10000
namespace NetHack.Sokoban41
open Diagram NetHack.Sokoban.LowerBounds
theorem goal0_semantic (pattern : Ten) : d793 pattern = (if budgetGuard 0 pattern && decide ((Projection.occupied pattern).length ≤ 1) then 1 else 0) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases c <;> cases d
    · exact goal0_shape0 e f g h i j
    · exact goal0_shape1 e f g h i j
    · exact goal0_shape2 e f g h i j
    · exact goal0_shape3 e f g h i j
    · exact goal0_shape4 e f g h i j
    · exact goal0_shape5 e f g h i j
    · exact goal0_shape6 e f g h i j
    · exact goal0_shape7 e f g h i j
    · exact goal0_shape8 e f g h i j
    · exact goal0_shape9 e f g h i j
    · exact goal0_shape10 e f g h i j
    · exact goal0_shape11 e f g h i j
    · exact goal0_shape12 e f g h i j
    · exact goal0_shape13 e f g h i j
    · exact goal0_shape14 e f g h i j
    · exact goal0_shape15 e f g h i j
theorem goal1_semantic (pattern : Ten) : d800 pattern = (if decide ((support.filter (fun cell => known pattern cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases c <;> cases d
    · exact goal1_shape0 e f g h i j
    · exact goal1_shape1 e f g h i j
    · exact goal1_shape2 e f g h i j
    · exact goal1_shape3 e f g h i j
    · exact goal1_shape4 e f g h i j
    · exact goal1_shape5 e f g h i j
    · exact goal1_shape6 e f g h i j
    · exact goal1_shape7 e f g h i j
    · exact goal1_shape8 e f g h i j
    · exact goal1_shape9 e f g h i j
    · exact goal1_shape10 e f g h i j
    · exact goal1_shape11 e f g h i j
    · exact goal1_shape12 e f g h i j
    · exact goal1_shape13 e f g h i j
    · exact goal1_shape14 e f g h i j
    · exact goal1_shape15 e f g h i j
theorem cap_semantic (pattern : Ten) : d816 pattern = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied pattern)) := by
  cases pattern with
  | mk a b c d e f g h i j =>
    cases a <;> cases b <;> cases c <;> cases d
    · exact cap_shape0 e f g h i j
    · exact cap_shape1 e f g h i j
    · exact cap_shape2 e f g h i j
    · exact cap_shape3 e f g h i j
    · exact cap_shape4 e f g h i j
    · exact cap_shape5 e f g h i j
    · exact cap_shape6 e f g h i j
    · exact cap_shape7 e f g h i j
    · exact cap_shape8 e f g h i j
    · exact cap_shape9 e f g h i j
    · exact cap_shape10 e f g h i j
    · exact cap_shape11 e f g h i j
    · exact cap_shape12 e f g h i j
    · exact cap_shape13 e f g h i j
    · exact cap_shape14 e f g h i j
    · exact cap_shape15 e f g h i j
private theorem if_le {P : Prop} [Decidable P] {a b z : Int}
    (left : a ≤ z) (right : b ≤ z) : (if P then a else b) ≤ z := by
  split <;> assumption
theorem root_goal0 (pattern : Ten) (guard : d793 pattern = 1) (player : Nat) :
    Diagram.root false player pattern ≤ d816 pattern := by
  unfold Diagram.root
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC63 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC63 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC63 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC81 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC63 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC94 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC63 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC127 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC154 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC172 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC175 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC185 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC63 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC33 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC199 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC211 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC63 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC228 pattern guard) (range816 pattern).1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem root_goal1 (pattern : Ten) (guard : d800 pattern = 1) (player : Nat) :
    Diagram.root true player pattern ≤ d816 pattern := by
  unfold Diagram.root
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC256 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC256 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC256 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC270 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC256 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC276 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC256 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC284 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC297 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC309 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC319 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC321 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC325 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC334 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC242 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC341 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC348 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC356 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (if_le (by simpa only [Int.zero_add] using goalC363 pattern guard) (range816 pattern).1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
end NetHack.Sokoban41
