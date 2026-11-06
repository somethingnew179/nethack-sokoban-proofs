/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.GoalDebtsChunks00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem debt_13_8 (p : Pattern) : d321 p = min (12 : Int) (8 + debt13 p) := by
  have shape : d321 p = (if p 224 then d12 p else d320 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_12]
    have h := min_cap_add (12 : Int) 8 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (8 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_13_9 (p : Pattern) : d358 p = min (12 : Int) (9 + debt13 p) := by
  have shape : d358 p = (if p 224 then d12 p else d357 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_12]
    have h := min_cap_add (12 : Int) 9 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (9 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_13_10 (p : Pattern) : d335 p = min (12 : Int) (10 + debt13 p) := by
  have shape : d335 p = (if p 224 then d12 p else d330 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_12]
    have h := min_cap_add (12 : Int) 10 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (10 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_13_11 (p : Pattern) : d333 p = min (12 : Int) (11 + debt13 p) := by
  have shape : d333 p = (if p 224 then d12 p else d332 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt13, Int.zero_add] using debt_14_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt13]
    rw [debt_14_12]
    have h := min_cap_add (12 : Int) 11 7 (debt14 p) (debt_nonnegative14 p)
    have literal : min (12 : Int) (11 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_13_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt13 p) := by
  change (12 : Int) = min 12 (12 + debt13 p)
  have h := debt_nonnegative13 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_12_0 (p : Pattern) : d322 p = min (12 : Int) (0 + debt12 p) := by
  have shape : d322 p = (if p 204 then d321 p else d319 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_8]
    have h := min_cap_add (12 : Int) 0 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (0 + 8) = 8 := by decide
    simpa only [literal] using h
theorem debt_12_1 (p : Pattern) : d432 p = min (12 : Int) (1 + debt12 p) := by
  have shape : d432 p = (if p 204 then d358 p else d431 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_9]
    have h := min_cap_add (12 : Int) 1 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (1 + 8) = 9 := by decide
    simpa only [literal] using h
theorem debt_12_2 (p : Pattern) : d382 p = min (12 : Int) (2 + debt12 p) := by
  have shape : d382 p = (if p 204 then d335 p else d381 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_10]
    have h := min_cap_add (12 : Int) 2 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (2 + 8) = 10 := by decide
    simpa only [literal] using h
theorem debt_12_3 (p : Pattern) : d334 p = min (12 : Int) (3 + debt12 p) := by
  have shape : d334 p = (if p 204 then d333 p else d331 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_11]
    have h := min_cap_add (12 : Int) 3 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (3 + 8) = 11 := by decide
    simpa only [literal] using h
theorem debt_12_4 (p : Pattern) : d342 p = min (12 : Int) (4 + debt12 p) := by
  have shape : d342 p = (if p 204 then d12 p else d341 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_12]
    have h := min_cap_add (12 : Int) 4 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (4 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_12_5 (p : Pattern) : d351 p = min (12 : Int) (5 + debt12 p) := by
  have shape : d351 p = (if p 204 then d12 p else d350 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_12]
    have h := min_cap_add (12 : Int) 5 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (5 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_12_6 (p : Pattern) : d367 p = min (12 : Int) (6 + debt12 p) := by
  have shape : d367 p = (if p 204 then d12 p else d366 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_12]
    have h := min_cap_add (12 : Int) 6 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (6 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_12_7 (p : Pattern) : d324 p = min (12 : Int) (7 + debt12 p) := by
  have shape : d324 p = (if p 204 then d12 p else d323 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_12]
    have h := min_cap_add (12 : Int) 7 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (7 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_12_8 (p : Pattern) : d353 p = min (12 : Int) (8 + debt12 p) := by
  have shape : d353 p = (if p 204 then d12 p else d321 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_12]
    have h := min_cap_add (12 : Int) 8 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (8 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_12_9 (p : Pattern) : d359 p = min (12 : Int) (9 + debt12 p) := by
  have shape : d359 p = (if p 204 then d12 p else d358 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_12]
    have h := min_cap_add (12 : Int) 9 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (9 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_12_10 (p : Pattern) : d336 p = min (12 : Int) (10 + debt12 p) := by
  have shape : d336 p = (if p 204 then d12 p else d335 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_12]
    have h := min_cap_add (12 : Int) 10 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (10 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_12_11 (p : Pattern) : d343 p = min (12 : Int) (11 + debt12 p) := by
  have shape : d343 p = (if p 204 then d12 p else d333 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt12, Int.zero_add] using debt_13_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt12]
    rw [debt_13_12]
    have h := min_cap_add (12 : Int) 11 8 (debt13 p) (debt_nonnegative13 p)
    have literal : min (12 : Int) (11 + 8) = 12 := by decide
    simpa only [literal] using h
theorem debt_12_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt12 p) := by
  change (12 : Int) = min 12 (12 + debt12 p)
  have h := debt_nonnegative12 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_11_0 (p : Pattern) : d325 p = min (12 : Int) (0 + debt11 p) := by
  have shape : d325 p = (if p 182 then d324 p else d322 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_7]
    have h := min_cap_add (12 : Int) 0 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (0 + 7) = 7 := by decide
    simpa only [literal] using h
theorem debt_11_1 (p : Pattern) : d433 p = min (12 : Int) (1 + debt11 p) := by
  have shape : d433 p = (if p 182 then d353 p else d432 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_8]
    have h := min_cap_add (12 : Int) 1 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (1 + 7) = 8 := by decide
    simpa only [literal] using h
theorem debt_11_2 (p : Pattern) : d383 p = min (12 : Int) (2 + debt11 p) := by
  have shape : d383 p = (if p 182 then d359 p else d382 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_9]
    have h := min_cap_add (12 : Int) 2 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (2 + 7) = 9 := by decide
    simpa only [literal] using h
theorem debt_11_3 (p : Pattern) : d337 p = min (12 : Int) (3 + debt11 p) := by
  have shape : d337 p = (if p 182 then d336 p else d334 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_10]
    have h := min_cap_add (12 : Int) 3 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (3 + 7) = 10 := by decide
    simpa only [literal] using h
theorem debt_11_4 (p : Pattern) : d344 p = min (12 : Int) (4 + debt11 p) := by
  have shape : d344 p = (if p 182 then d343 p else d342 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_11]
    have h := min_cap_add (12 : Int) 4 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (4 + 7) = 11 := by decide
    simpa only [literal] using h
theorem debt_11_5 (p : Pattern) : d352 p = min (12 : Int) (5 + debt11 p) := by
  have shape : d352 p = (if p 182 then d12 p else d351 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_12]
    have h := min_cap_add (12 : Int) 5 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (5 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_11_6 (p : Pattern) : d368 p = min (12 : Int) (6 + debt11 p) := by
  have shape : d368 p = (if p 182 then d12 p else d367 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_12]
    have h := min_cap_add (12 : Int) 6 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (6 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_11_7 (p : Pattern) : d345 p = min (12 : Int) (7 + debt11 p) := by
  have shape : d345 p = (if p 182 then d12 p else d324 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_12]
    have h := min_cap_add (12 : Int) 7 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (7 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_11_8 (p : Pattern) : d354 p = min (12 : Int) (8 + debt11 p) := by
  have shape : d354 p = (if p 182 then d12 p else d353 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_12]
    have h := min_cap_add (12 : Int) 8 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (8 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_11_9 (p : Pattern) : d360 p = min (12 : Int) (9 + debt11 p) := by
  have shape : d360 p = (if p 182 then d12 p else d359 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_12]
    have h := min_cap_add (12 : Int) 9 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (9 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_11_10 (p : Pattern) : d370 p = min (12 : Int) (10 + debt11 p) := by
  have shape : d370 p = (if p 182 then d12 p else d336 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_12]
    have h := min_cap_add (12 : Int) 10 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (10 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_11_11 (p : Pattern) : d373 p = min (12 : Int) (11 + debt11 p) := by
  have shape : d373 p = (if p 182 then d12 p else d343 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt11, Int.zero_add] using debt_12_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt11]
    rw [debt_12_12]
    have h := min_cap_add (12 : Int) 11 7 (debt12 p) (debt_nonnegative12 p)
    have literal : min (12 : Int) (11 + 7) = 12 := by decide
    simpa only [literal] using h
theorem debt_11_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt11 p) := by
  change (12 : Int) = min 12 (12 + debt11 p)
  have h := debt_nonnegative11 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_10_0 (p : Pattern) : d338 p = min (12 : Int) (0 + debt10 p) := by
  have shape : d338 p = (if p 163 then d337 p else d325 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_3]
    have h := min_cap_add (12 : Int) 0 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (0 + 3) = 3 := by decide
    simpa only [literal] using h
theorem debt_10_1 (p : Pattern) : d434 p = min (12 : Int) (1 + debt10 p) := by
  have shape : d434 p = (if p 163 then d344 p else d433 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_4]
    have h := min_cap_add (12 : Int) 1 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (1 + 3) = 4 := by decide
    simpa only [literal] using h
theorem debt_10_2 (p : Pattern) : d384 p = min (12 : Int) (2 + debt10 p) := by
  have shape : d384 p = (if p 163 then d352 p else d383 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_5]
    have h := min_cap_add (12 : Int) 2 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (2 + 3) = 5 := by decide
    simpa only [literal] using h
theorem debt_10_3 (p : Pattern) : d415 p = min (12 : Int) (3 + debt10 p) := by
  have shape : d415 p = (if p 163 then d368 p else d337 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_6]
    have h := min_cap_add (12 : Int) 3 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (3 + 3) = 6 := by decide
    simpa only [literal] using h
theorem debt_10_4 (p : Pattern) : d346 p = min (12 : Int) (4 + debt10 p) := by
  have shape : d346 p = (if p 163 then d345 p else d344 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_7]
    have h := min_cap_add (12 : Int) 4 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (4 + 3) = 7 := by decide
    simpa only [literal] using h
theorem debt_10_5 (p : Pattern) : d355 p = min (12 : Int) (5 + debt10 p) := by
  have shape : d355 p = (if p 163 then d354 p else d352 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_8]
    have h := min_cap_add (12 : Int) 5 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (5 + 3) = 8 := by decide
    simpa only [literal] using h
theorem debt_10_6 (p : Pattern) : d369 p = min (12 : Int) (6 + debt10 p) := by
  have shape : d369 p = (if p 163 then d360 p else d368 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_9]
    have h := min_cap_add (12 : Int) 6 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (6 + 3) = 9 := by decide
    simpa only [literal] using h
theorem debt_10_7 (p : Pattern) : d386 p = min (12 : Int) (7 + debt10 p) := by
  have shape : d386 p = (if p 163 then d370 p else d345 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_10]
    have h := min_cap_add (12 : Int) 7 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (7 + 3) = 10 := by decide
    simpa only [literal] using h
theorem debt_10_8 (p : Pattern) : d389 p = min (12 : Int) (8 + debt10 p) := by
  have shape : d389 p = (if p 163 then d373 p else d354 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_11]
    have h := min_cap_add (12 : Int) 8 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (8 + 3) = 11 := by decide
    simpa only [literal] using h
theorem debt_10_9 (p : Pattern) : d361 p = min (12 : Int) (9 + debt10 p) := by
  have shape : d361 p = (if p 163 then d12 p else d360 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_12]
    have h := min_cap_add (12 : Int) 9 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (9 + 3) = 12 := by decide
    simpa only [literal] using h
theorem debt_10_10 (p : Pattern) : d371 p = min (12 : Int) (10 + debt10 p) := by
  have shape : d371 p = (if p 163 then d12 p else d370 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_12]
    have h := min_cap_add (12 : Int) 10 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (10 + 3) = 12 := by decide
    simpa only [literal] using h
theorem debt_10_11 (p : Pattern) : d374 p = min (12 : Int) (11 + debt10 p) := by
  have shape : d374 p = (if p 163 then d12 p else d373 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt10, Int.zero_add] using debt_11_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt10]
    rw [debt_11_12]
    have h := min_cap_add (12 : Int) 11 3 (debt11 p) (debt_nonnegative11 p)
    have literal : min (12 : Int) (11 + 3) = 12 := by decide
    simpa only [literal] using h
theorem debt_10_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt10 p) := by
  change (12 : Int) = min 12 (12 + debt10 p)
  have h := debt_nonnegative10 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_9_0 (p : Pattern) : d347 p = min (12 : Int) (0 + debt9 p) := by
  have shape : d347 p = (if p 162 then d346 p else d338 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_4]
    have h := min_cap_add (12 : Int) 0 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (0 + 4) = 4 := by decide
    simpa only [literal] using h
theorem debt_9_1 (p : Pattern) : d435 p = min (12 : Int) (1 + debt9 p) := by
  have shape : d435 p = (if p 162 then d355 p else d434 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_5]
    have h := min_cap_add (12 : Int) 1 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (1 + 4) = 5 := by decide
    simpa only [literal] using h
theorem debt_9_2 (p : Pattern) : d385 p = min (12 : Int) (2 + debt9 p) := by
  have shape : d385 p = (if p 162 then d369 p else d384 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_6]
    have h := min_cap_add (12 : Int) 2 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (2 + 4) = 6 := by decide
    simpa only [literal] using h
theorem debt_9_3 (p : Pattern) : d416 p = min (12 : Int) (3 + debt9 p) := by
  have shape : d416 p = (if p 162 then d386 p else d415 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_7]
    have h := min_cap_add (12 : Int) 3 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (3 + 4) = 7 := by decide
    simpa only [literal] using h
theorem debt_9_4 (p : Pattern) : d402 p = min (12 : Int) (4 + debt9 p) := by
  have shape : d402 p = (if p 162 then d389 p else d346 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_8]
    have h := min_cap_add (12 : Int) 4 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (4 + 4) = 8 := by decide
    simpa only [literal] using h
theorem debt_9_5 (p : Pattern) : d362 p = min (12 : Int) (5 + debt9 p) := by
  have shape : d362 p = (if p 162 then d361 p else d355 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_9]
    have h := min_cap_add (12 : Int) 5 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (5 + 4) = 9 := by decide
    simpa only [literal] using h
theorem debt_9_6 (p : Pattern) : d372 p = min (12 : Int) (6 + debt9 p) := by
  have shape : d372 p = (if p 162 then d371 p else d369 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_6 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_10]
    have h := min_cap_add (12 : Int) 6 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (6 + 4) = 10 := by decide
    simpa only [literal] using h
theorem debt_9_7 (p : Pattern) : d387 p = min (12 : Int) (7 + debt9 p) := by
  have shape : d387 p = (if p 162 then d374 p else d386 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_7 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_11]
    have h := min_cap_add (12 : Int) 7 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (7 + 4) = 11 := by decide
    simpa only [literal] using h
theorem debt_9_8 (p : Pattern) : d390 p = min (12 : Int) (8 + debt9 p) := by
  have shape : d390 p = (if p 162 then d12 p else d389 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_8 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_12]
    have h := min_cap_add (12 : Int) 8 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (8 + 4) = 12 := by decide
    simpa only [literal] using h
theorem debt_9_9 (p : Pattern) : d403 p = min (12 : Int) (9 + debt9 p) := by
  have shape : d403 p = (if p 162 then d12 p else d361 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_9 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_12]
    have h := min_cap_add (12 : Int) 9 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (9 + 4) = 12 := by decide
    simpa only [literal] using h
theorem debt_9_10 (p : Pattern) : d394 p = min (12 : Int) (10 + debt9 p) := by
  have shape : d394 p = (if p 162 then d12 p else d371 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_10 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_12]
    have h := min_cap_add (12 : Int) 10 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (10 + 4) = 12 := by decide
    simpa only [literal] using h
theorem debt_9_11 (p : Pattern) : d375 p = min (12 : Int) (11 + debt9 p) := by
  have shape : d375 p = (if p 162 then d12 p else d374 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt9, Int.zero_add] using debt_10_11 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt9]
    rw [debt_10_12]
    have h := min_cap_add (12 : Int) 11 4 (debt10 p) (debt_nonnegative10 p)
    have literal : min (12 : Int) (11 + 4) = 12 := by decide
    simpa only [literal] using h
theorem debt_9_12 (p : Pattern) : d12 p = min (12 : Int) (12 + debt9 p) := by
  change (12 : Int) = min 12 (12 + debt9 p)
  have h := debt_nonnegative9 p
  exact (Int.min_eq_left (by omega)).symm
theorem debt_8_0 (p : Pattern) : d363 p = min (12 : Int) (0 + debt8 p) := by
  have shape : d363 p = (if p 161 then d362 p else d347 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_5]
    have h := min_cap_add (12 : Int) 0 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (0 + 5) = 5 := by decide
    simpa only [literal] using h
theorem debt_8_1 (p : Pattern) : d436 p = min (12 : Int) (1 + debt8 p) := by
  have shape : d436 p = (if p 161 then d372 p else d435 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_6]
    have h := min_cap_add (12 : Int) 1 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (1 + 5) = 6 := by decide
    simpa only [literal] using h
theorem debt_8_2 (p : Pattern) : d388 p = min (12 : Int) (2 + debt8 p) := by
  have shape : d388 p = (if p 161 then d387 p else d385 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, debt8, Int.zero_add] using debt_9_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, debt8]
    rw [debt_9_7]
    have h := min_cap_add (12 : Int) 2 5 (debt9 p) (debt_nonnegative9 p)
    have literal : min (12 : Int) (2 + 5) = 7 := by decide
    simpa only [literal] using h
end NetHack.Sokoban22Refined85
