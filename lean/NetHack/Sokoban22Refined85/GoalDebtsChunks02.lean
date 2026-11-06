/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.GoalDebtsChunks01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem debt_8_3 (p : Pattern) : d417 p = min (12 : Int) (3 + debt8 p) := by
  have shape : d417 p = (if p 161 then d390 p else d416 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_8]
    have h := min_cap_add (12 : Int) 3 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (3 + 5) = 8 := by decide
    simpa only [literal] using h
theorem debt_8_4 (p : Pattern) : d404 p = min (12 : Int) (4 + debt8 p) := by
  have shape : d404 p = (if p 161 then d403 p else d402 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_9]
    have h := min_cap_add (12 : Int) 4 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (4 + 5) = 9 := by decide
    simpa only [literal] using h
theorem debt_8_5 (p : Pattern) : d395 p = min (12 : Int) (5 + debt8 p) := by
  have shape : d395 p = (if p 161 then d394 p else d362 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_10]
    have h := min_cap_add (12 : Int) 5 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (5 + 5) = 10 := by decide
    simpa only [literal] using h
theorem debt_8_6 (p : Pattern) : d376 p = min (12 : Int) (6 + debt8 p) := by
  have shape : d376 p = (if p 161 then d375 p else d372 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_11]
    have h := min_cap_add (12 : Int) 6 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (6 + 5) = 11 := by decide
    simpa only [literal] using h
theorem debt_8_7 (p : Pattern) : d398 p = min (12 : Int) (7 + debt8 p) := by
  have shape : d398 p = (if p 161 then d12 p else d387 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_12]
    have h := min_cap_add (12 : Int) 7 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (7 + 5) = 12 := by decide
    simpa only [literal] using h
theorem debt_8_8 (p : Pattern) : d391 p = min (12 : Int) (8 + debt8 p) := by
  have shape : d391 p = (if p 161 then d12 p else d390 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_12]
    have h := min_cap_add (12 : Int) 8 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (8 + 5) = 12 := by decide
    simpa only [literal] using h
theorem debt_8_9 (p : Pattern) : d409 p = min (12 : Int) (9 + debt8 p) := by
  have shape : d409 p = (if p 161 then d12 p else d403 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_12]
    have h := min_cap_add (12 : Int) 9 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (9 + 5) = 12 := by decide
    simpa only [literal] using h
theorem debt_8_10 (p : Pattern) : d405 p = min (12 : Int) (10 + debt8 p) := by
  have shape : d405 p = (if p 161 then d12 p else d394 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_12]
    have h := min_cap_add (12 : Int) 10 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (10 + 5) = 12 := by decide
    simpa only [literal] using h
theorem debt_8_11 (p : Pattern) : d396 p = min (12 : Int) (11 + debt8 p) := by
  have shape : d396 p = (if p 161 then d12 p else d375 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_12]
    have h := min_cap_add (12 : Int) 11 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (11 + 5) = 12 := by decide
    simpa only [literal] using h
theorem debt_8_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt8 p) := by
  change (12 : Int) = min 12 (12 + debt8 p)
  have h := debt_nonnegative8 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_7_0 (p : Pattern) : d377 p = min (12 : Int) (0 + debt7 p) := by
  have shape : d377 p = (if p 160 then d376 p else d363 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_6]
    have h := min_cap_add (12 : Int) 0 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (0 + 6) = 6 := by decide
    simpa only [literal] using h
theorem debt_7_1 (p : Pattern) : d437 p = min (12 : Int) (1 + debt7 p) := by
  have shape : d437 p = (if p 160 then d398 p else d436 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_7]
    have h := min_cap_add (12 : Int) 1 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (1 + 6) = 7 := by decide
    simpa only [literal] using h
theorem debt_7_2 (p : Pattern) : d392 p = min (12 : Int) (2 + debt7 p) := by
  have shape : d392 p = (if p 160 then d391 p else d388 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_8]
    have h := min_cap_add (12 : Int) 2 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (2 + 6) = 8 := by decide
    simpa only [literal] using h
theorem debt_7_3 (p : Pattern) : d418 p = min (12 : Int) (3 + debt7 p) := by
  have shape : d418 p = (if p 160 then d409 p else d417 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_9]
    have h := min_cap_add (12 : Int) 3 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (3 + 6) = 9 := by decide
    simpa only [literal] using h
theorem debt_7_4 (p : Pattern) : d406 p = min (12 : Int) (4 + debt7 p) := by
  have shape : d406 p = (if p 160 then d405 p else d404 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_10]
    have h := min_cap_add (12 : Int) 4 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (4 + 6) = 10 := by decide
    simpa only [literal] using h
theorem debt_7_5 (p : Pattern) : d397 p = min (12 : Int) (5 + debt7 p) := by
  have shape : d397 p = (if p 160 then d396 p else d395 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_11]
    have h := min_cap_add (12 : Int) 5 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (5 + 6) = 11 := by decide
    simpa only [literal] using h
theorem debt_7_6 (p : Pattern) : d407 p = min (12 : Int) (6 + debt7 p) := by
  have shape : d407 p = (if p 160 then d12 p else d376 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_12]
    have h := min_cap_add (12 : Int) 6 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (6 + 6) = 12 := by decide
    simpa only [literal] using h
theorem debt_7_7 (p : Pattern) : d399 p = min (12 : Int) (7 + debt7 p) := by
  have shape : d399 p = (if p 160 then d12 p else d398 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_12]
    have h := min_cap_add (12 : Int) 7 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (7 + 6) = 12 := by decide
    simpa only [literal] using h
theorem debt_7_8 (p : Pattern) : d420 p = min (12 : Int) (8 + debt7 p) := by
  have shape : d420 p = (if p 160 then d12 p else d391 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_12]
    have h := min_cap_add (12 : Int) 8 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (8 + 6) = 12 := by decide
    simpa only [literal] using h
theorem debt_7_9 (p : Pattern) : d410 p = min (12 : Int) (9 + debt7 p) := by
  have shape : d410 p = (if p 160 then d12 p else d409 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_12]
    have h := min_cap_add (12 : Int) 9 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (9 + 6) = 12 := by decide
    simpa only [literal] using h
theorem debt_7_10 (p : Pattern) : d421 p = min (12 : Int) (10 + debt7 p) := by
  have shape : d421 p = (if p 160 then d12 p else d405 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_12]
    have h := min_cap_add (12 : Int) 10 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (10 + 6) = 12 := by decide
    simpa only [literal] using h
theorem debt_7_11 (p : Pattern) : d411 p = min (12 : Int) (11 + debt7 p) := by
  have shape : d411 p = (if p 160 then d12 p else d396 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt7, Int.zero_add] using debt_8_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt7]
    rw [debt_8_12]
    have h := min_cap_add (12 : Int) 11 6 (debt8 p) (debt_nonnegative8 p)
    have literal : min (12 : Int) (11 + 6) = 12 := by decide
    simpa only [literal] using h
theorem debt_7_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt7 p) := by
  change (12 : Int) = min 12 (12 + debt7 p)
  have h := debt_nonnegative7 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_6_0 (p : Pattern) : d393 p = min (12 : Int) (0 + debt6 p) := by
  have shape : d393 p = (if p 141 then d392 p else d377 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_2]
    have h := min_cap_add (12 : Int) 0 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (0 + 2) = 2 := by decide
    simpa only [literal] using h
theorem debt_6_1 (p : Pattern) : d438 p = min (12 : Int) (1 + debt6 p) := by
  have shape : d438 p = (if p 141 then d418 p else d437 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_3]
    have h := min_cap_add (12 : Int) 1 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (1 + 2) = 3 := by decide
    simpa only [literal] using h
theorem debt_6_3 (p : Pattern) : d419 p = min (12 : Int) (3 + debt6 p) := by
  have shape : d419 p = (if p 141 then d397 p else d418 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_5]
    have h := min_cap_add (12 : Int) 3 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (3 + 2) = 5 := by decide
    simpa only [literal] using h
theorem debt_6_4 (p : Pattern) : d408 p = min (12 : Int) (4 + debt6 p) := by
  have shape : d408 p = (if p 141 then d407 p else d406 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_6]
    have h := min_cap_add (12 : Int) 4 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (4 + 2) = 6 := by decide
    simpa only [literal] using h
theorem debt_6_5 (p : Pattern) : d400 p = min (12 : Int) (5 + debt6 p) := by
  have shape : d400 p = (if p 141 then d399 p else d397 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_7]
    have h := min_cap_add (12 : Int) 5 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (5 + 2) = 7 := by decide
    simpa only [literal] using h
theorem debt_6_6 (p : Pattern) : d439 p = min (12 : Int) (6 + debt6 p) := by
  have shape : d439 p = (if p 141 then d420 p else d407 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_8]
    have h := min_cap_add (12 : Int) 6 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (6 + 2) = 8 := by decide
    simpa only [literal] using h
theorem debt_6_7 (p : Pattern) : d424 p = min (12 : Int) (7 + debt6 p) := by
  have shape : d424 p = (if p 141 then d410 p else d399 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_9]
    have h := min_cap_add (12 : Int) 7 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (7 + 2) = 9 := by decide
    simpa only [literal] using h
theorem debt_6_8 (p : Pattern) : d422 p = min (12 : Int) (8 + debt6 p) := by
  have shape : d422 p = (if p 141 then d421 p else d420 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_10]
    have h := min_cap_add (12 : Int) 8 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (8 + 2) = 10 := by decide
    simpa only [literal] using h
theorem debt_6_9 (p : Pattern) : d412 p = min (12 : Int) (9 + debt6 p) := by
  have shape : d412 p = (if p 141 then d411 p else d410 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_11]
    have h := min_cap_add (12 : Int) 9 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (9 + 2) = 11 := by decide
    simpa only [literal] using h
theorem debt_6_10 (p : Pattern) : d441 p = min (12 : Int) (10 + debt6 p) := by
  have shape : d441 p = (if p 141 then d12 p else d421 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt6, Int.zero_add] using debt_7_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt6]
    rw [debt_7_12]
    have h := min_cap_add (12 : Int) 10 2 (debt7 p) (debt_nonnegative7 p)
    have literal : min (12 : Int) (10 + 2) = 12 := by decide
    simpa only [literal] using h
theorem debt_6_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt6 p) := by
  change (12 : Int) = min 12 (12 + debt6 p)
  have h := debt_nonnegative6 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_5_0 (p : Pattern) : d401 p = min (12 : Int) (0 + debt5 p) := by
  have shape : d401 p = (if p 138 then d400 p else d393 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_5]
    have h := min_cap_add (12 : Int) 0 5 (debt6 p) (debt_nonnegative6 p)
    have literal : min (12 : Int) (0 + 5) = 5 := by decide
    simpa only [literal] using h
theorem debt_5_1 (p : Pattern) : d440 p = min (12 : Int) (1 + debt5 p) := by
  have shape : d440 p = (if p 138 then d439 p else d438 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_6]
    have h := min_cap_add (12 : Int) 1 5 (debt6 p) (debt_nonnegative6 p)
    have literal : min (12 : Int) (1 + 5) = 6 := by decide
    simpa only [literal] using h
theorem debt_5_3 (p : Pattern) : d423 p = min (12 : Int) (3 + debt5 p) := by
  have shape : d423 p = (if p 138 then d422 p else d419 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_8]
    have h := min_cap_add (12 : Int) 3 5 (debt6 p) (debt_nonnegative6 p)
    have literal : min (12 : Int) (3 + 5) = 8 := by decide
    simpa only [literal] using h
theorem debt_5_4 (p : Pattern) : d413 p = min (12 : Int) (4 + debt5 p) := by
  have shape : d413 p = (if p 138 then d412 p else d408 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_9]
    have h := min_cap_add (12 : Int) 4 5 (debt6 p) (debt_nonnegative6 p)
    have literal : min (12 : Int) (4 + 5) = 9 := by decide
    simpa only [literal] using h
theorem debt_5_5 (p : Pattern) : d442 p = min (12 : Int) (5 + debt5 p) := by
  have shape : d442 p = (if p 138 then d441 p else d400 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_10]
    have h := min_cap_add (12 : Int) 5 5 (debt6 p) (debt_nonnegative6 p)
    have literal : min (12 : Int) (5 + 5) = 10 := by decide
    simpa only [literal] using h
theorem debt_5_7 (p : Pattern) : d425 p = min (12 : Int) (7 + debt5 p) := by
  have shape : d425 p = (if p 138 then d12 p else d424 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_12]
    have h := min_cap_add (12 : Int) 7 5 (debt6 p) (debt_nonnegative6 p)
    have literal : min (12 : Int) (7 + 5) = 12 := by decide
    simpa only [literal] using h
theorem debt_5_8 (p : Pattern) : d444 p = min (12 : Int) (8 + debt5 p) := by
  have shape : d444 p = (if p 138 then d12 p else d422 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt5, Int.zero_add] using debt_6_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt5]
    rw [debt_6_12]
    have h := min_cap_add (12 : Int) 8 5 (debt6 p) (debt_nonnegative6 p)
    have literal : min (12 : Int) (8 + 5) = 12 := by decide
    simpa only [literal] using h
theorem debt_4_0 (p : Pattern) : d414 p = min (12 : Int) (0 + debt4 p) := by
  have shape : d414 p = (if p 116 then d413 p else d401 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt4, Int.zero_add] using debt_5_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt4]
    rw [debt_5_4]
    have h := min_cap_add (12 : Int) 0 4 (debt5 p) (debt_nonnegative5 p)
    have literal : min (12 : Int) (0 + 4) = 4 := by decide
    simpa only [literal] using h
theorem debt_4_1 (p : Pattern) : d443 p = min (12 : Int) (1 + debt4 p) := by
  have shape : d443 p = (if p 116 then d442 p else d440 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt4, Int.zero_add] using debt_5_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt4]
    rw [debt_5_5]
    have h := min_cap_add (12 : Int) 1 4 (debt5 p) (debt_nonnegative5 p)
    have literal : min (12 : Int) (1 + 4) = 5 := by decide
    simpa only [literal] using h
theorem debt_4_3 (p : Pattern) : d426 p = min (12 : Int) (3 + debt4 p) := by
  have shape : d426 p = (if p 116 then d425 p else d423 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt4, Int.zero_add] using debt_5_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt4]
    rw [debt_5_7]
    have h := min_cap_add (12 : Int) 3 4 (debt5 p) (debt_nonnegative5 p)
    have literal : min (12 : Int) (3 + 4) = 7 := by decide
    simpa only [literal] using h
theorem debt_4_4 (p : Pattern) : d445 p = min (12 : Int) (4 + debt4 p) := by
  have shape : d445 p = (if p 116 then d444 p else d413 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt4, Int.zero_add] using debt_5_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt4]
    rw [debt_5_8]
    have h := min_cap_add (12 : Int) 4 4 (debt5 p) (debt_nonnegative5 p)
    have literal : min (12 : Int) (4 + 4) = 8 := by decide
    simpa only [literal] using h
theorem debt_3_0 (p : Pattern) : d427 p = min (12 : Int) (0 + debt3 p) := by
  have shape : d427 p = (if p 115 then d426 p else d414 p) := by rfl
  rw [shape]
  cases selected : p 115 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt3, Int.zero_add] using debt_4_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt3]
    rw [debt_4_3]
    have h := min_cap_add (12 : Int) 0 3 (debt4 p) (debt_nonnegative4 p)
    have literal : min (12 : Int) (0 + 3) = 3 := by decide
    simpa only [literal] using h
theorem debt_3_1 (p : Pattern) : d446 p = min (12 : Int) (1 + debt3 p) := by
  have shape : d446 p = (if p 115 then d445 p else d443 p) := by rfl
  rw [shape]
  cases selected : p 115 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt3, Int.zero_add] using debt_4_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt3]
    rw [debt_4_4]
    have h := min_cap_add (12 : Int) 1 3 (debt4 p) (debt_nonnegative4 p)
    have literal : min (12 : Int) (1 + 3) = 4 := by decide
    simpa only [literal] using h
theorem debt_2_0 (p : Pattern) : d447 p = min (12 : Int) (0 + debt2 p) := by
  have shape : d447 p = (if p 71 then d446 p else d427 p) := by rfl
  rw [shape]
  cases selected : p 71 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt2, Int.zero_add] using debt_3_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt2]
    rw [debt_3_1]
    have h := min_cap_add (12 : Int) 0 1 (debt3 p) (debt_nonnegative3 p)
    have literal : min (12 : Int) (0 + 1) = 1 := by decide
    simpa only [literal] using h
theorem debt_1_0 (p : Pattern) : d447 p = min (12 : Int) (0 + debt1 p) := by
  have shape : d447 p = (if p 49 then d447 p else d447 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 49 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt1, Int.zero_add] using debt_2_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt1]
    rw [debt_2_0]
    have h := min_cap_add (12 : Int) 0 0 (debt2 p) (debt_nonnegative2 p)
    have literal : min (12 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
theorem debt_0_0 (p : Pattern) : d447 p = min (12 : Int) (0 + debt0 p) := by
  have shape : d447 p = (if p 48 then d447 p else d447 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 48 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt0, Int.zero_add] using debt_1_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt0]
    rw [debt_1_0]
    have h := min_cap_add (12 : Int) 0 0 (debt1 p) (debt_nonnegative1 p)
    have literal : min (12 : Int) (0 + 0) = 0 := by decide
    simpa only [literal] using h
end NetHack.Sokoban22Refined85
