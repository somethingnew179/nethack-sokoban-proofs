/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.GoalBudgets
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem debt_14_0 (p : Pattern) : d0 p = min (5 : Int) (0 + debt14 p) := by
  change (0 : Int) = min 5 (0 + 0)
  decide
theorem debt_14_2 (p : Pattern) : d2 p = min (5 : Int) (2 + debt14 p) := by
  change (2 : Int) = min 5 (2 + 0)
  decide
theorem debt_14_3 (p : Pattern) : d3 p = min (5 : Int) (3 + debt14 p) := by
  change (3 : Int) = min 5 (3 + 0)
  decide
theorem debt_13_0 (p : Pattern) : d0 p = min (5 : Int) (0 + debt13 p) := by
  have shape : d0 p = (if p 271 then d0 p else d0 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 271 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_0]
    have h := min_cap_add (5 : Int) 0 0 (debt14 p) (debt_nonnegative14 p)
    have literal : min (5 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_13_2 (p : Pattern) : d2 p = min (5 : Int) (2 + debt13 p) := by
  have shape : d2 p = (if p 271 then d2 p else d2 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 271 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_2]
    have h := min_cap_add (5 : Int) 2 0 (debt14 p) (debt_nonnegative14 p)
    have literal : min (5 : Int) (2 + 0) = 2 := by decide
    simpa only [literal] using h
theorem debt_13_3 (p : Pattern) : d3 p = min (5 : Int) (3 + debt13 p) := by
  have shape : d3 p = (if p 271 then d3 p else d3 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 271 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_3]
    have h := min_cap_add (5 : Int) 3 0 (debt14 p) (debt_nonnegative14 p)
    have literal : min (5 : Int) (3 + 0) = 3 := by decide
    simpa only [literal] using h
theorem debt_13_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt13 p) := by
  change (5 : Int) = min 5 (5 + debt13 p)
  have h := debt_nonnegative13 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_12_0 (p : Pattern) : d6 p = min (5 : Int) (0 + debt12 p) := by
  have shape : d6 p = (if p 193 then d2 p else d0 p) := by rfl
  rw [shape]
  cases selected : p 193 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_2]
    have h := min_cap_add (5 : Int) 0 2 (debt13 p) (debt_nonnegative13 p)
    have literal : min (5 : Int) (0 + 2) = 2 := by decide
    simpa only [literal] using h
theorem debt_12_3 (p : Pattern) : d1237 p = min (5 : Int) (3 + debt12 p) := by
  have shape : d1237 p = (if p 193 then d5 p else d3 p) := by rfl
  rw [shape]
  cases selected : p 193 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_5]
    have h := min_cap_add (5 : Int) 3 2 (debt13 p) (debt_nonnegative13 p)
    have literal : min (5 : Int) (3 + 2) = 5 := by decide
    simpa only [literal] using h
theorem debt_11_0 (p : Pattern) : d1344 p = min (5 : Int) (0 + debt11 p) := by
  have shape : d1344 p = (if p 192 then d1237 p else d6 p) := by rfl
  rw [shape]
  cases selected : p 192 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_3]
    have h := min_cap_add (5 : Int) 0 3 (debt12 p) (debt_nonnegative12 p)
    have literal : min (5 : Int) (0 + 3) = 3 := by decide
    simpa only [literal] using h
theorem debt_11_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt11 p) := by
  change (5 : Int) = min 5 (5 + debt11 p)
  have h := debt_nonnegative11 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_10_0 (p : Pattern) : d1345 p = min (5 : Int) (0 + debt10 p) := by
  have shape : d1345 p = (if p 187 then d5 p else d1344 p) := by rfl
  rw [shape]
  cases selected : p 187 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_5]
    have h := min_cap_add (5 : Int) 0 8 (debt11 p) (debt_nonnegative11 p)
    have literal : min (5 : Int) (0 + 8) = 5 := by decide
    simpa only [literal] using h
theorem debt_10_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt10 p) := by
  change (5 : Int) = min 5 (5 + debt10 p)
  have h := debt_nonnegative10 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_9_0 (p : Pattern) : d1346 p = min (5 : Int) (0 + debt9 p) := by
  have shape : d1346 p = (if p 186 then d5 p else d1345 p) := by rfl
  rw [shape]
  cases selected : p 186 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_5]
    have h := min_cap_add (5 : Int) 0 11 (debt10 p) (debt_nonnegative10 p)
    have literal : min (5 : Int) (0 + 11) = 5 := by decide
    simpa only [literal] using h
theorem debt_8_0 (p : Pattern) : d1346 p = min (5 : Int) (0 + debt8 p) := by
  have shape : d1346 p = (if p 168 then d1346 p else d1346 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 168 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_0]
    have h := min_cap_add (5 : Int) 0 0 (debt9 p) (debt_nonnegative9 p)
    have literal : min (5 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_8_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt8 p) := by
  change (5 : Int) = min 5 (5 + debt8 p)
  have h := debt_nonnegative8 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_7_0 (p : Pattern) : d1347 p = min (5 : Int) (0 + debt7 p) := by
  have shape : d1347 p = (if p 160 then d5 p else d1346 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_5]
    have h := min_cap_add (5 : Int) 0 12 (debt8 p) (debt_nonnegative8 p)
    have literal : min (5 : Int) (0 + 12) = 5 := by decide
    simpa only [literal] using h
theorem debt_7_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt7 p) := by
  change (5 : Int) = min 5 (5 + debt7 p)
  have h := debt_nonnegative7 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_6_0 (p : Pattern) : d1348 p = min (5 : Int) (0 + debt6 p) := by
  have shape : d1348 p = (if p 159 then d5 p else d1347 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_5]
    have h := min_cap_add (5 : Int) 0 11 (debt7 p) (debt_nonnegative7 p)
    have literal : min (5 : Int) (0 + 11) = 5 := by decide
    simpa only [literal] using h
theorem debt_6_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt6 p) := by
  change (5 : Int) = min 5 (5 + debt6 p)
  have h := debt_nonnegative6 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_5_0 (p : Pattern) : d1349 p = min (5 : Int) (0 + debt5 p) := by
  have shape : d1349 p = (if p 158 then d5 p else d1348 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_5]
    have h := min_cap_add (5 : Int) 0 10 (debt6 p) (debt_nonnegative6 p)
    have literal : min (5 : Int) (0 + 10) = 5 := by decide
    simpa only [literal] using h
theorem debt_4_0 (p : Pattern) : d1349 p = min (5 : Int) (0 + debt4 p) := by
  have shape : d1349 p = (if p 141 then d1349 p else d1349 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt4, Int.zero_add] using debt_5_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt4]
    rw [debt_5_0]
    have h := min_cap_add (5 : Int) 0 0 (debt5 p) (debt_nonnegative5 p)
    have literal : min (5 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_4_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt4 p) := by
  change (5 : Int) = min 5 (5 + debt4 p)
  have h := debt_nonnegative4 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_3_0 (p : Pattern) : d1350 p = min (5 : Int) (0 + debt3 p) := by
  have shape : d1350 p = (if p 134 then d5 p else d1349 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt3, Int.zero_add] using debt_4_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt3]
    rw [debt_4_5]
    have h := min_cap_add (5 : Int) 0 13 (debt4 p) (debt_nonnegative4 p)
    have literal : min (5 : Int) (0 + 13) = 5 := by decide
    simpa only [literal] using h
theorem debt_3_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt3 p) := by
  change (5 : Int) = min 5 (5 + debt3 p)
  have h := debt_nonnegative3 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_2_0 (p : Pattern) : d1351 p = min (5 : Int) (0 + debt2 p) := by
  have shape : d1351 p = (if p 133 then d5 p else d1350 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt2, Int.zero_add] using debt_3_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt2]
    rw [debt_3_5]
    have h := min_cap_add (5 : Int) 0 12 (debt3 p) (debt_nonnegative3 p)
    have literal : min (5 : Int) (0 + 12) = 5 := by decide
    simpa only [literal] using h
theorem debt_2_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt2 p) := by
  change (5 : Int) = min 5 (5 + debt2 p)
  have h := debt_nonnegative2 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_1_0 (p : Pattern) : d1352 p = min (5 : Int) (0 + debt1 p) := by
  have shape : d1352 p = (if p 132 then d5 p else d1351 p) := by rfl
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt1, Int.zero_add] using debt_2_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt1]
    rw [debt_2_5]
    have h := min_cap_add (5 : Int) 0 11 (debt2 p) (debt_nonnegative2 p)
    have literal : min (5 : Int) (0 + 11) = 5 := by decide
    simpa only [literal] using h
theorem debt_1_5 (p : Pattern) : d5 p = min (5 : Int) (5 + debt1 p) := by
  change (5 : Int) = min 5 (5 + debt1 p)
  have h := debt_nonnegative1 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_0_0 (p : Pattern) : d1353 p = min (5 : Int) (0 + debt0 p) := by
  have shape : d1353 p = (if p 108 then d5 p else d1352 p) := by rfl
  rw [shape]
  cases selected : p 108 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt0, Int.zero_add] using debt_1_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt0]
    rw [debt_1_5]
    have h := min_cap_add (5 : Int) 0 14 (debt1 p) (debt_nonnegative1 p)
    have literal : min (5 : Int) (0 + 14) = 5 := by decide
    simpa only [literal] using h
end NetHack.Sokoban12CostPartition
