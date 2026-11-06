/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.GoalBudgets
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem debt_17_0 (p : Pattern) : d0 p = min (12 : Int) (0 + debt17 p) := by
  change (0 : Int) = min 12 (0 + 0)
  decide
theorem debt_17_1 (p : Pattern) : d1 p = min (12 : Int) (1 + debt17 p) := by
  change (1 : Int) = min 12 (1 + 0)
  decide
theorem debt_17_2 (p : Pattern) : d2 p = min (12 : Int) (2 + debt17 p) := by
  change (2 : Int) = min 12 (2 + 0)
  decide
theorem debt_17_3 (p : Pattern) : d3 p = min (12 : Int) (3 + debt17 p) := by
  change (3 : Int) = min 12 (3 + 0)
  decide
theorem debt_17_4 (p : Pattern) : d4 p = min (12 : Int) (4 + debt17 p) := by
  change (4 : Int) = min 12 (4 + 0)
  decide
theorem debt_17_5 (p : Pattern) : d5 p = min (12 : Int) (5 + debt17 p) := by
  change (5 : Int) = min 12 (5 + 0)
  decide
theorem debt_17_6 (p : Pattern) : d6 p = min (12 : Int) (6 + debt17 p) := by
  change (6 : Int) = min 12 (6 + 0)
  decide
theorem debt_17_7 (p : Pattern) : d7 p = min (12 : Int) (7 + debt17 p) := by
  change (7 : Int) = min 12 (7 + 0)
  decide
theorem debt_17_8 (p : Pattern) : d8 p = min (12 : Int) (8 + debt17 p) := by
  change (8 : Int) = min 12 (8 + 0)
  decide
theorem debt_17_9 (p : Pattern) : d9 p = min (12 : Int) (9 + debt17 p) := by
  change (9 : Int) = min 12 (9 + 0)
  decide
theorem debt_17_10 (p : Pattern) : d10 p = min (12 : Int) (10 + debt17 p) := by
  change (10 : Int) = min 12 (10 + 0)
  decide
theorem debt_17_11 (p : Pattern) : d11 p = min (12 : Int) (11 + debt17 p) := by
  change (11 : Int) = min 12 (11 + 0)
  decide
theorem debt_17_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt17 p) := by
  change (12 : Int) = min 12 (12 + debt17 p)
  have h := debt_nonnegative17 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_16_0 (p : Pattern) : d313 p = min (12 : Int) (0 + debt16 p) := by
  have shape : d313 p = (if p 247 then d9 p else d0 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_9]
    have h := min_cap_add (12 : Int) 0 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (0 + 9) = 9 := by decide
    simpa only [literal] using h
theorem debt_16_1 (p : Pattern) : d428 p = min (12 : Int) (1 + debt16 p) := by
  have shape : d428 p = (if p 247 then d10 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_10]
    have h := min_cap_add (12 : Int) 1 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (1 + 9) = 10 := by decide
    simpa only [literal] using h
theorem debt_16_2 (p : Pattern) : d378 p = min (12 : Int) (2 + debt16 p) := by
  have shape : d378 p = (if p 247 then d11 p else d2 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_11]
    have h := min_cap_add (12 : Int) 2 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (2 + 9) = 11 := by decide
    simpa only [literal] using h
theorem debt_16_3 (p : Pattern) : d115 p = min (12 : Int) (3 + debt16 p) := by
  have shape : d115 p = (if p 247 then d12 p else d3 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 3 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (3 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_4 (p : Pattern) : d17 p = min (12 : Int) (4 + debt16 p) := by
  have shape : d17 p = (if p 247 then d12 p else d4 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 4 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (4 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_5 (p : Pattern) : d106 p = min (12 : Int) (5 + debt16 p) := by
  have shape : d106 p = (if p 247 then d12 p else d5 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 5 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (5 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_6 (p : Pattern) : d34 p = min (12 : Int) (6 + debt16 p) := by
  have shape : d34 p = (if p 247 then d12 p else d6 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 6 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (6 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_7 (p : Pattern) : d119 p = min (12 : Int) (7 + debt16 p) := by
  have shape : d119 p = (if p 247 then d12 p else d7 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 7 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (7 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_8 (p : Pattern) : d190 p = min (12 : Int) (8 + debt16 p) := by
  have shape : d190 p = (if p 247 then d12 p else d8 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 8 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (8 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_9 (p : Pattern) : d23 p = min (12 : Int) (9 + debt16 p) := by
  have shape : d23 p = (if p 247 then d12 p else d9 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 9 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (9 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_10 (p : Pattern) : d57 p = min (12 : Int) (10 + debt16 p) := by
  have shape : d57 p = (if p 247 then d12 p else d10 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 10 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (10 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_11 (p : Pattern) : d39 p = min (12 : Int) (11 + debt16 p) := by
  have shape : d39 p = (if p 247 then d12 p else d11 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt16, Int.zero_add] using debt_17_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt16]
    rw [debt_17_12]
    have h := min_cap_add (12 : Int) 11 9 (debt17 p) (debt_nonnegative17 p)
    have literal : min (12 : Int) (11 + 9) = 12 := by decide
    simpa only [literal] using h
theorem debt_16_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt16 p) := by
  change (12 : Int) = min 12 (12 + debt16 p)
  have h := debt_nonnegative16 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_15_0 (p : Pattern) : d314 p = min (12 : Int) (0 + debt15 p) := by
  have shape : d314 p = (if p 246 then d190 p else d313 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_8]
    have h := min_cap_add (12 : Int) 0 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (0 + 8) = 8 := by decide
    simpa only [literal] using h
theorem debt_15_1 (p : Pattern) : d429 p = min (12 : Int) (1 + debt15 p) := by
  have shape : d429 p = (if p 246 then d23 p else d428 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_9]
    have h := min_cap_add (12 : Int) 1 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (1 + 8) = 9 := by decide
    simpa only [literal] using h
theorem debt_15_2 (p : Pattern) : d379 p = min (12 : Int) (2 + debt15 p) := by
  have shape : d379 p = (if p 246 then d57 p else d378 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_10]
    have h := min_cap_add (12 : Int) 2 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (2 + 8) = 10 := by decide
    simpa only [literal] using h
theorem debt_15_3 (p : Pattern) : d326 p = min (12 : Int) (3 + debt15 p) := by
  have shape : d326 p = (if p 246 then d39 p else d115 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_11]
    have h := min_cap_add (12 : Int) 3 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (3 + 8) = 11 := by decide
    simpa only [literal] using h
theorem debt_15_4 (p : Pattern) : d339 p = min (12 : Int) (4 + debt15 p) := by
  have shape : d339 p = (if p 246 then d12 p else d17 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_12]
    have h := min_cap_add (12 : Int) 4 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (4 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_15_5 (p : Pattern) : d348 p = min (12 : Int) (5 + debt15 p) := by
  have shape : d348 p = (if p 246 then d12 p else d106 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_12]
    have h := min_cap_add (12 : Int) 5 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (5 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_15_6 (p : Pattern) : d364 p = min (12 : Int) (6 + debt15 p) := by
  have shape : d364 p = (if p 246 then d12 p else d34 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_12]
    have h := min_cap_add (12 : Int) 6 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (6 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_15_7 (p : Pattern) : d317 p = min (12 : Int) (7 + debt15 p) := by
  have shape : d317 p = (if p 246 then d12 p else d119 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_12]
    have h := min_cap_add (12 : Int) 7 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (7 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_15_8 (p : Pattern) : d315 p = min (12 : Int) (8 + debt15 p) := by
  have shape : d315 p = (if p 246 then d12 p else d190 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_12]
    have h := min_cap_add (12 : Int) 8 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (8 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_15_9 (p : Pattern) : d356 p = min (12 : Int) (9 + debt15 p) := by
  have shape : d356 p = (if p 246 then d12 p else d23 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_12]
    have h := min_cap_add (12 : Int) 9 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (9 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_15_10 (p : Pattern) : d329 p = min (12 : Int) (10 + debt15 p) := by
  have shape : d329 p = (if p 246 then d12 p else d57 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_12]
    have h := min_cap_add (12 : Int) 10 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (10 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_15_11 (p : Pattern) : d327 p = min (12 : Int) (11 + debt15 p) := by
  have shape : d327 p = (if p 246 then d12 p else d39 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt15, Int.zero_add] using debt_16_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt15]
    rw [debt_16_12]
    have h := min_cap_add (12 : Int) 11 8 (debt16 p) (debt_nonnegative16 p)
    have literal : min (12 : Int) (11 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_15_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt15 p) := by
  change (12 : Int) = min 12 (12 + debt15 p)
  have h := debt_nonnegative15 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_14_0 (p : Pattern) : d316 p = min (12 : Int) (0 + debt14 p) := by
  have shape : d316 p = (if p 225 then d315 p else d314 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_8]
    have h := min_cap_add (12 : Int) 0 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (0 + 8) = 8 := by decide
    simpa only [literal] using h
theorem debt_14_1 (p : Pattern) : d430 p = min (12 : Int) (1 + debt14 p) := by
  have shape : d430 p = (if p 225 then d356 p else d429 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_9]
    have h := min_cap_add (12 : Int) 1 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (1 + 8) = 9 := by decide
    simpa only [literal] using h
theorem debt_14_2 (p : Pattern) : d380 p = min (12 : Int) (2 + debt14 p) := by
  have shape : d380 p = (if p 225 then d329 p else d379 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_10]
    have h := min_cap_add (12 : Int) 2 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (2 + 8) = 10 := by decide
    simpa only [literal] using h
theorem debt_14_3 (p : Pattern) : d328 p = min (12 : Int) (3 + debt14 p) := by
  have shape : d328 p = (if p 225 then d327 p else d326 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_11]
    have h := min_cap_add (12 : Int) 3 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (3 + 8) = 11 := by decide
    simpa only [literal] using h
theorem debt_14_4 (p : Pattern) : d340 p = min (12 : Int) (4 + debt14 p) := by
  have shape : d340 p = (if p 225 then d12 p else d339 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_12]
    have h := min_cap_add (12 : Int) 4 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (4 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_14_5 (p : Pattern) : d349 p = min (12 : Int) (5 + debt14 p) := by
  have shape : d349 p = (if p 225 then d12 p else d348 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_12]
    have h := min_cap_add (12 : Int) 5 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (5 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_14_6 (p : Pattern) : d365 p = min (12 : Int) (6 + debt14 p) := by
  have shape : d365 p = (if p 225 then d12 p else d364 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_12]
    have h := min_cap_add (12 : Int) 6 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (6 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_14_7 (p : Pattern) : d318 p = min (12 : Int) (7 + debt14 p) := by
  have shape : d318 p = (if p 225 then d12 p else d317 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_12]
    have h := min_cap_add (12 : Int) 7 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (7 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_14_8 (p : Pattern) : d320 p = min (12 : Int) (8 + debt14 p) := by
  have shape : d320 p = (if p 225 then d12 p else d315 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_12]
    have h := min_cap_add (12 : Int) 8 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (8 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_14_9 (p : Pattern) : d357 p = min (12 : Int) (9 + debt14 p) := by
  have shape : d357 p = (if p 225 then d12 p else d356 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_12]
    have h := min_cap_add (12 : Int) 9 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (9 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_14_10 (p : Pattern) : d330 p = min (12 : Int) (10 + debt14 p) := by
  have shape : d330 p = (if p 225 then d12 p else d329 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_12]
    have h := min_cap_add (12 : Int) 10 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (10 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_14_11 (p : Pattern) : d332 p = min (12 : Int) (11 + debt14 p) := by
  have shape : d332 p = (if p 225 then d12 p else d327 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt14, Int.zero_add] using debt_15_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt14]
    rw [debt_15_12]
    have h := min_cap_add (12 : Int) 11 8 (debt15 p) (debt_nonnegative15 p)
    have literal : min (12 : Int) (11 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_14_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt14 p) := by
  change (12 : Int) = min 12 (12 + debt14 p)
  have h := debt_nonnegative14 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_13_0 (p : Pattern) : d319 p = min (12 : Int) (0 + debt13 p) := by
  have shape : d319 p = (if p 224 then d318 p else d316 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_7]
    have h := min_cap_add (12 : Int) 0 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (0 + 7) = 7 := by decide
    simpa only [literal] using h
theorem debt_13_1 (p : Pattern) : d431 p = min (12 : Int) (1 + debt13 p) := by
  have shape : d431 p = (if p 224 then d320 p else d430 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_8]
    have h := min_cap_add (12 : Int) 1 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (1 + 7) = 8 := by decide
    simpa only [literal] using h
theorem debt_13_2 (p : Pattern) : d381 p = min (12 : Int) (2 + debt13 p) := by
  have shape : d381 p = (if p 224 then d357 p else d380 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_9]
    have h := min_cap_add (12 : Int) 2 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (2 + 7) = 9 := by decide
    simpa only [literal] using h
theorem debt_13_3 (p : Pattern) : d331 p = min (12 : Int) (3 + debt13 p) := by
  have shape : d331 p = (if p 224 then d330 p else d328 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_10]
    have h := min_cap_add (12 : Int) 3 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (3 + 7) = 10 := by decide
    simpa only [literal] using h
theorem debt_13_4 (p : Pattern) : d341 p = min (12 : Int) (4 + debt13 p) := by
  have shape : d341 p = (if p 224 then d332 p else d340 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_11]
    have h := min_cap_add (12 : Int) 4 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (4 + 7) = 11 := by decide
    simpa only [literal] using h
theorem debt_13_5 (p : Pattern) : d350 p = min (12 : Int) (5 + debt13 p) := by
  have shape : d350 p = (if p 224 then d12 p else d349 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_12]
    have h := min_cap_add (12 : Int) 5 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (5 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_13_6 (p : Pattern) : d366 p = min (12 : Int) (6 + debt13 p) := by
  have shape : d366 p = (if p 224 then d12 p else d365 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_12]
    have h := min_cap_add (12 : Int) 6 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (6 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_13_7 (p : Pattern) : d323 p = min (12 : Int) (7 + debt13 p) := by
  have shape : d323 p = (if p 224 then d12 p else d318 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_12]
    have h := min_cap_add (12 : Int) 7 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (7 + 7) = 12 := by decide
    simpa only [literal] using h
end NetHack.Sokoban22Refined85
