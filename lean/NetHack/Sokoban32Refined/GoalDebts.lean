/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.GoalBudgets
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem debt_14_0 (p : Pattern) : d0 p = min (2 : Int) (0 + debt14 p) := by
  change (0 : Int) = min 2 (0 + 0)
  decide
theorem debt_14_1 (p : Pattern) : d1 p = min (2 : Int) (1 + debt14 p) := by
  change (1 : Int) = min 2 (1 + 0)
  decide
theorem debt_14_2 (p : Pattern) : d2 p = min (2 : Int) (2 + debt14 p) := by
  change (2 : Int) = min 2 (2 + debt14 p)
  have h := debt_nonnegative14 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_13_0 (p : Pattern) : d3 p = min (2 : Int) (0 + debt13 p) := by
  have shape : d3 p = (if p 161 then d2 p else d0 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_2]
    have h := min_cap_add (2 : Int) 0 4 (debt14 p) (debt_nonnegative14 p)
    have literal : min (2 : Int) (0 + 4) = 2 := by decide
    simpa only [literal] using h
theorem debt_13_1 (p : Pattern) : d9 p = min (2 : Int) (1 + debt13 p) := by
  have shape : d9 p = (if p 161 then d2 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_2]
    have h := min_cap_add (2 : Int) 1 4 (debt14 p) (debt_nonnegative14 p)
    have literal : min (2 : Int) (1 + 4) = 2 := by decide
    simpa only [literal] using h
theorem debt_13_2 (p : Pattern) : d2 p = min (2 : Int) (2 + debt13 p) := by
  change (2 : Int) = min 2 (2 + debt13 p)
  have h := debt_nonnegative13 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_12_0 (p : Pattern) : d17 p = min (2 : Int) (0 + debt12 p) := by
  have shape : d17 p = (if p 160 then d2 p else d3 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_2]
    have h := min_cap_add (2 : Int) 0 3 (debt13 p) (debt_nonnegative13 p)
    have literal : min (2 : Int) (0 + 3) = 2 := by decide
    simpa only [literal] using h
theorem debt_12_1 (p : Pattern) : d21 p = min (2 : Int) (1 + debt12 p) := by
  have shape : d21 p = (if p 160 then d2 p else d9 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_2]
    have h := min_cap_add (2 : Int) 1 3 (debt13 p) (debt_nonnegative13 p)
    have literal : min (2 : Int) (1 + 3) = 2 := by decide
    simpa only [literal] using h
theorem debt_12_2 (p : Pattern) : d2 p = min (2 : Int) (2 + debt12 p) := by
  change (2 : Int) = min 2 (2 + debt12 p)
  have h := debt_nonnegative12 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_11_0 (p : Pattern) : d19 p = min (2 : Int) (0 + debt11 p) := by
  have shape : d19 p = (if p 159 then d2 p else d17 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_2]
    have h := min_cap_add (2 : Int) 0 2 (debt12 p) (debt_nonnegative12 p)
    have literal : min (2 : Int) (0 + 2) = 2 := by decide
    simpa only [literal] using h
theorem debt_11_1 (p : Pattern) : d23 p = min (2 : Int) (1 + debt11 p) := by
  have shape : d23 p = (if p 159 then d2 p else d21 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_2]
    have h := min_cap_add (2 : Int) 1 2 (debt12 p) (debt_nonnegative12 p)
    have literal : min (2 : Int) (1 + 2) = 2 := by decide
    simpa only [literal] using h
theorem debt_11_2 (p : Pattern) : d2 p = min (2 : Int) (2 + debt11 p) := by
  change (2 : Int) = min 2 (2 + debt11 p)
  have h := debt_nonnegative11 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_10_0 (p : Pattern) : d135 p = min (2 : Int) (0 + debt10 p) := by
  have shape : d135 p = (if p 158 then d23 p else d19 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_1]
    have h := min_cap_add (2 : Int) 0 1 (debt11 p) (debt_nonnegative11 p)
    have literal : min (2 : Int) (0 + 1) = 1 := by decide
    simpa only [literal] using h
theorem debt_10_1 (p : Pattern) : d138 p = min (2 : Int) (1 + debt10 p) := by
  have shape : d138 p = (if p 158 then d2 p else d23 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_2]
    have h := min_cap_add (2 : Int) 1 1 (debt11 p) (debt_nonnegative11 p)
    have literal : min (2 : Int) (1 + 1) = 2 := by decide
    simpa only [literal] using h
theorem debt_9_0 (p : Pattern) : d135 p = min (2 : Int) (0 + debt9 p) := by
  have shape : d135 p = (if p 139 then d135 p else d135 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 139 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_0]
    have h := min_cap_add (2 : Int) 0 0 (debt10 p) (debt_nonnegative10 p)
    have literal : min (2 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_9_1 (p : Pattern) : d138 p = min (2 : Int) (1 + debt9 p) := by
  have shape : d138 p = (if p 139 then d138 p else d138 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 139 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_1]
    have h := min_cap_add (2 : Int) 1 0 (debt10 p) (debt_nonnegative10 p)
    have literal : min (2 : Int) (1 + 0) = 1 := by decide
    simpa only [literal] using h
theorem debt_9_2 (p : Pattern) : d2 p = min (2 : Int) (2 + debt9 p) := by
  change (2 : Int) = min 2 (2 + debt9 p)
  have h := debt_nonnegative9 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_8_0 (p : Pattern) : d136 p = min (2 : Int) (0 + debt8 p) := by
  have shape : d136 p = (if p 138 then d2 p else d135 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_2]
    have h := min_cap_add (2 : Int) 0 2 (debt9 p) (debt_nonnegative9 p)
    have literal : min (2 : Int) (0 + 2) = 2 := by decide
    simpa only [literal] using h
theorem debt_8_1 (p : Pattern) : d139 p = min (2 : Int) (1 + debt8 p) := by
  have shape : d139 p = (if p 138 then d2 p else d138 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_2]
    have h := min_cap_add (2 : Int) 1 2 (debt9 p) (debt_nonnegative9 p)
    have literal : min (2 : Int) (1 + 2) = 2 := by decide
    simpa only [literal] using h
theorem debt_8_2 (p : Pattern) : d2 p = min (2 : Int) (2 + debt8 p) := by
  change (2 : Int) = min 2 (2 + debt8 p)
  have h := debt_nonnegative8 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_7_0 (p : Pattern) : d137 p = min (2 : Int) (0 + debt7 p) := by
  have shape : d137 p = (if p 134 then d2 p else d136 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_2]
    have h := min_cap_add (2 : Int) 0 2 (debt8 p) (debt_nonnegative8 p)
    have literal : min (2 : Int) (0 + 2) = 2 := by decide
    simpa only [literal] using h
theorem debt_7_1 (p : Pattern) : d140 p = min (2 : Int) (1 + debt7 p) := by
  have shape : d140 p = (if p 134 then d2 p else d139 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_2]
    have h := min_cap_add (2 : Int) 1 2 (debt8 p) (debt_nonnegative8 p)
    have literal : min (2 : Int) (1 + 2) = 2 := by decide
    simpa only [literal] using h
theorem debt_7_2 (p : Pattern) : d2 p = min (2 : Int) (2 + debt7 p) := by
  change (2 : Int) = min 2 (2 + debt7 p)
  have h := debt_nonnegative7 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_6_0 (p : Pattern) : d141 p = min (2 : Int) (0 + debt6 p) := by
  have shape : d141 p = (if p 133 then d140 p else d137 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_1]
    have h := min_cap_add (2 : Int) 0 1 (debt7 p) (debt_nonnegative7 p)
    have literal : min (2 : Int) (0 + 1) = 1 := by decide
    simpa only [literal] using h
theorem debt_6_1 (p : Pattern) : d152 p = min (2 : Int) (1 + debt6 p) := by
  have shape : d152 p = (if p 133 then d2 p else d140 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_2]
    have h := min_cap_add (2 : Int) 1 1 (debt7 p) (debt_nonnegative7 p)
    have literal : min (2 : Int) (1 + 1) = 2 := by decide
    simpa only [literal] using h
theorem debt_5_0 (p : Pattern) : d141 p = min (2 : Int) (0 + debt5 p) := by
  have shape : d141 p = (if p 132 then d141 p else d141 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_0]
    have h := min_cap_add (2 : Int) 0 0 (debt6 p) (debt_nonnegative6 p)
    have literal : min (2 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_5_1 (p : Pattern) : d152 p = min (2 : Int) (1 + debt5 p) := by
  have shape : d152 p = (if p 132 then d152 p else d152 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_1]
    have h := min_cap_add (2 : Int) 1 0 (debt6 p) (debt_nonnegative6 p)
    have literal : min (2 : Int) (1 + 0) = 1 := by decide
    simpa only [literal] using h
theorem debt_4_0 (p : Pattern) : d141 p = min (2 : Int) (0 + debt4 p) := by
  have shape : d141 p = (if p 113 then d141 p else d141 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 113 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt4, Int.zero_add] using debt_5_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt4]
    rw [debt_5_0]
    have h := min_cap_add (2 : Int) 0 0 (debt5 p) (debt_nonnegative5 p)
    have literal : min (2 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_4_1 (p : Pattern) : d152 p = min (2 : Int) (1 + debt4 p) := by
  have shape : d152 p = (if p 113 then d152 p else d152 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 113 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt4, Int.zero_add] using debt_5_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt4]
    rw [debt_5_1]
    have h := min_cap_add (2 : Int) 1 0 (debt5 p) (debt_nonnegative5 p)
    have literal : min (2 : Int) (1 + 0) = 1 := by decide
    simpa only [literal] using h
theorem debt_3_0 (p : Pattern) : d1991 p = min (2 : Int) (0 + debt3 p) := by
  have shape : d1991 p = (if p 112 then d152 p else d141 p) := by rfl
  rw [shape]
  cases selected : p 112 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt3, Int.zero_add] using debt_4_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt3]
    rw [debt_4_1]
    have h := min_cap_add (2 : Int) 0 1 (debt4 p) (debt_nonnegative4 p)
    have literal : min (2 : Int) (0 + 1) = 1 := by decide
    simpa only [literal] using h
theorem debt_2_0 (p : Pattern) : d1991 p = min (2 : Int) (0 + debt2 p) := by
  have shape : d1991 p = (if p 106 then d1991 p else d1991 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 106 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt2, Int.zero_add] using debt_3_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt2]
    rw [debt_3_0]
    have h := min_cap_add (2 : Int) 0 0 (debt3 p) (debt_nonnegative3 p)
    have literal : min (2 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_1_0 (p : Pattern) : d1991 p = min (2 : Int) (0 + debt1 p) := by
  have shape : d1991 p = (if p 86 then d1991 p else d1991 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 86 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt1, Int.zero_add] using debt_2_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt1]
    rw [debt_2_0]
    have h := min_cap_add (2 : Int) 0 0 (debt2 p) (debt_nonnegative2 p)
    have literal : min (2 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_0_0 (p : Pattern) : d1991 p = min (2 : Int) (0 + debt0 p) := by
  have shape : d1991 p = (if p 80 then d1991 p else d1991 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 80 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt0, Int.zero_add] using debt_1_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt0]
    rw [debt_1_0]
    have h := min_cap_add (2 : Int) 0 0 (debt1 p) (debt_nonnegative1 p)
    have literal : min (2 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
end NetHack.Sokoban32Refined
