/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.GoalExpressions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem budget_17_0 (p : Pattern) : d1 p = 1 ↔ count17 p ≤ 0 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 0)
  decide
theorem budget_17_1 (p : Pattern) : d1 p = 1 ↔ count17 p ≤ 1 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 1)
  decide
theorem budget_17_2 (p : Pattern) : d1 p = 1 ↔ count17 p ≤ 2 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 2)
  decide
theorem budget_17_3 (p : Pattern) : d1 p = 1 ↔ count17 p ≤ 3 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 3)
  decide
theorem budget_17_4 (p : Pattern) : d1 p = 1 ↔ count17 p ≤ 4 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 4)
  decide
theorem budget_17_5 (p : Pattern) : d1 p = 1 ↔ count17 p ≤ 5 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 5)
  decide
theorem budget_16_0 (p : Pattern) : d5843 p = 1 ↔ count16 p ≤ 0 := by
  have shape : d5843 p = (if p 247 then d0 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count16, Nat.zero_add] using budget_17_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count16]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_16_1 (p : Pattern) : d1 p = 1 ↔ count16 p ≤ 1 := by
  have shape : d1 p = (if p 247 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count16, Nat.zero_add] using budget_17_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count16]
    have h := budget_17_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_16_2 (p : Pattern) : d1 p = 1 ↔ count16 p ≤ 2 := by
  have shape : d1 p = (if p 247 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count16, Nat.zero_add] using budget_17_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count16]
    have h := budget_17_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_16_3 (p : Pattern) : d1 p = 1 ↔ count16 p ≤ 3 := by
  have shape : d1 p = (if p 247 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count16, Nat.zero_add] using budget_17_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count16]
    have h := budget_17_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_16_4 (p : Pattern) : d1 p = 1 ↔ count16 p ≤ 4 := by
  have shape : d1 p = (if p 247 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count16, Nat.zero_add] using budget_17_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count16]
    have h := budget_17_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_16_5 (p : Pattern) : d1 p = 1 ↔ count16 p ≤ 5 := by
  have shape : d1 p = (if p 247 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 247 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count16, Nat.zero_add] using budget_17_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count16]
    have h := budget_17_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_15_0 (p : Pattern) : d5847 p = 1 ↔ count15 p ≤ 0 := by
  have shape : d5847 p = (if p 246 then d0 p else d5843 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count15, Nat.zero_add] using budget_16_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count15]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_15_1 (p : Pattern) : d8084 p = 1 ↔ count15 p ≤ 1 := by
  have shape : d8084 p = (if p 246 then d5843 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count15, Nat.zero_add] using budget_16_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count15]
    have h := budget_16_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_15_2 (p : Pattern) : d1 p = 1 ↔ count15 p ≤ 2 := by
  have shape : d1 p = (if p 246 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count15, Nat.zero_add] using budget_16_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count15]
    have h := budget_16_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_15_3 (p : Pattern) : d1 p = 1 ↔ count15 p ≤ 3 := by
  have shape : d1 p = (if p 246 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count15, Nat.zero_add] using budget_16_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count15]
    have h := budget_16_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_15_4 (p : Pattern) : d1 p = 1 ↔ count15 p ≤ 4 := by
  have shape : d1 p = (if p 246 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count15, Nat.zero_add] using budget_16_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count15]
    have h := budget_16_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_15_5 (p : Pattern) : d1 p = 1 ↔ count15 p ≤ 5 := by
  have shape : d1 p = (if p 246 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 246 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count15, Nat.zero_add] using budget_16_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count15]
    have h := budget_16_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_14_0 (p : Pattern) : d5854 p = 1 ↔ count14 p ≤ 0 := by
  have shape : d5854 p = (if p 225 then d0 p else d5847 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count14, Nat.zero_add] using budget_15_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count14]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_14_1 (p : Pattern) : d8089 p = 1 ↔ count14 p ≤ 1 := by
  have shape : d8089 p = (if p 225 then d5847 p else d8084 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count14, Nat.zero_add] using budget_15_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count14]
    have h := budget_15_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_14_2 (p : Pattern) : d8085 p = 1 ↔ count14 p ≤ 2 := by
  have shape : d8085 p = (if p 225 then d8084 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count14, Nat.zero_add] using budget_15_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count14]
    have h := budget_15_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_14_3 (p : Pattern) : d1 p = 1 ↔ count14 p ≤ 3 := by
  have shape : d1 p = (if p 225 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count14, Nat.zero_add] using budget_15_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count14]
    have h := budget_15_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_14_4 (p : Pattern) : d1 p = 1 ↔ count14 p ≤ 4 := by
  have shape : d1 p = (if p 225 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count14, Nat.zero_add] using budget_15_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count14]
    have h := budget_15_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_14_5 (p : Pattern) : d1 p = 1 ↔ count14 p ≤ 5 := by
  have shape : d1 p = (if p 225 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 225 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count14, Nat.zero_add] using budget_15_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count14]
    have h := budget_15_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_0 (p : Pattern) : d8099 p = 1 ↔ count13 p ≤ 0 := by
  have shape : d8099 p = (if p 224 then d0 p else d5854 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_13_1 (p : Pattern) : d8094 p = 1 ↔ count13 p ≤ 1 := by
  have shape : d8094 p = (if p 224 then d5854 p else d8089 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_2 (p : Pattern) : d8090 p = 1 ↔ count13 p ≤ 2 := by
  have shape : d8090 p = (if p 224 then d8089 p else d8085 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_3 (p : Pattern) : d8086 p = 1 ↔ count13 p ≤ 3 := by
  have shape : d8086 p = (if p 224 then d8085 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_4 (p : Pattern) : d1 p = 1 ↔ count13 p ≤ 4 := by
  have shape : d1 p = (if p 224 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_5 (p : Pattern) : d1 p = 1 ↔ count13 p ≤ 5 := by
  have shape : d1 p = (if p 224 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 224 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_0 (p : Pattern) : d8105 p = 1 ↔ count12 p ≤ 0 := by
  have shape : d8105 p = (if p 204 then d0 p else d8099 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_12_1 (p : Pattern) : d8100 p = 1 ↔ count12 p ≤ 1 := by
  have shape : d8100 p = (if p 204 then d8099 p else d8094 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_2 (p : Pattern) : d8095 p = 1 ↔ count12 p ≤ 2 := by
  have shape : d8095 p = (if p 204 then d8094 p else d8090 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_3 (p : Pattern) : d8091 p = 1 ↔ count12 p ≤ 3 := by
  have shape : d8091 p = (if p 204 then d8090 p else d8086 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_4 (p : Pattern) : d8087 p = 1 ↔ count12 p ≤ 4 := by
  have shape : d8087 p = (if p 204 then d8086 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_5 (p : Pattern) : d1 p = 1 ↔ count12 p ≤ 5 := by
  have shape : d1 p = (if p 204 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 204 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_0 (p : Pattern) : d8111 p = 1 ↔ count11 p ≤ 0 := by
  have shape : d8111 p = (if p 182 then d0 p else d8105 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_11_1 (p : Pattern) : d8106 p = 1 ↔ count11 p ≤ 1 := by
  have shape : d8106 p = (if p 182 then d8105 p else d8100 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_2 (p : Pattern) : d8101 p = 1 ↔ count11 p ≤ 2 := by
  have shape : d8101 p = (if p 182 then d8100 p else d8095 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_3 (p : Pattern) : d8096 p = 1 ↔ count11 p ≤ 3 := by
  have shape : d8096 p = (if p 182 then d8095 p else d8091 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_4 (p : Pattern) : d8092 p = 1 ↔ count11 p ≤ 4 := by
  have shape : d8092 p = (if p 182 then d8091 p else d8087 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_5 (p : Pattern) : d8088 p = 1 ↔ count11 p ≤ 5 := by
  have shape : d8088 p = (if p 182 then d8087 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 182 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_0 (p : Pattern) : d8117 p = 1 ↔ count10 p ≤ 0 := by
  have shape : d8117 p = (if p 163 then d0 p else d8111 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_10_1 (p : Pattern) : d8112 p = 1 ↔ count10 p ≤ 1 := by
  have shape : d8112 p = (if p 163 then d8111 p else d8106 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_2 (p : Pattern) : d8107 p = 1 ↔ count10 p ≤ 2 := by
  have shape : d8107 p = (if p 163 then d8106 p else d8101 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_3 (p : Pattern) : d8102 p = 1 ↔ count10 p ≤ 3 := by
  have shape : d8102 p = (if p 163 then d8101 p else d8096 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_4 (p : Pattern) : d8097 p = 1 ↔ count10 p ≤ 4 := by
  have shape : d8097 p = (if p 163 then d8096 p else d8092 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_5 (p : Pattern) : d8093 p = 1 ↔ count10 p ≤ 5 := by
  have shape : d8093 p = (if p 163 then d8092 p else d8088 p) := by rfl
  rw [shape]
  cases selected : p 163 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_0 (p : Pattern) : d8123 p = 1 ↔ count9 p ≤ 0 := by
  have shape : d8123 p = (if p 162 then d0 p else d8117 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_9_1 (p : Pattern) : d8118 p = 1 ↔ count9 p ≤ 1 := by
  have shape : d8118 p = (if p 162 then d8117 p else d8112 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_2 (p : Pattern) : d8113 p = 1 ↔ count9 p ≤ 2 := by
  have shape : d8113 p = (if p 162 then d8112 p else d8107 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_3 (p : Pattern) : d8108 p = 1 ↔ count9 p ≤ 3 := by
  have shape : d8108 p = (if p 162 then d8107 p else d8102 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_4 (p : Pattern) : d8103 p = 1 ↔ count9 p ≤ 4 := by
  have shape : d8103 p = (if p 162 then d8102 p else d8097 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_5 (p : Pattern) : d8098 p = 1 ↔ count9 p ≤ 5 := by
  have shape : d8098 p = (if p 162 then d8097 p else d8093 p) := by rfl
  rw [shape]
  cases selected : p 162 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_0 (p : Pattern) : d8129 p = 1 ↔ count8 p ≤ 0 := by
  have shape : d8129 p = (if p 161 then d0 p else d8123 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_8_1 (p : Pattern) : d8124 p = 1 ↔ count8 p ≤ 1 := by
  have shape : d8124 p = (if p 161 then d8123 p else d8118 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_2 (p : Pattern) : d8119 p = 1 ↔ count8 p ≤ 2 := by
  have shape : d8119 p = (if p 161 then d8118 p else d8113 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_3 (p : Pattern) : d8114 p = 1 ↔ count8 p ≤ 3 := by
  have shape : d8114 p = (if p 161 then d8113 p else d8108 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_4 (p : Pattern) : d8109 p = 1 ↔ count8 p ≤ 4 := by
  have shape : d8109 p = (if p 161 then d8108 p else d8103 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_5 (p : Pattern) : d8104 p = 1 ↔ count8 p ≤ 5 := by
  have shape : d8104 p = (if p 161 then d8103 p else d8098 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_0 (p : Pattern) : d8135 p = 1 ↔ count7 p ≤ 0 := by
  have shape : d8135 p = (if p 160 then d0 p else d8129 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_7_1 (p : Pattern) : d8130 p = 1 ↔ count7 p ≤ 1 := by
  have shape : d8130 p = (if p 160 then d8129 p else d8124 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_2 (p : Pattern) : d8125 p = 1 ↔ count7 p ≤ 2 := by
  have shape : d8125 p = (if p 160 then d8124 p else d8119 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_3 (p : Pattern) : d8120 p = 1 ↔ count7 p ≤ 3 := by
  have shape : d8120 p = (if p 160 then d8119 p else d8114 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_4 (p : Pattern) : d8115 p = 1 ↔ count7 p ≤ 4 := by
  have shape : d8115 p = (if p 160 then d8114 p else d8109 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_5 (p : Pattern) : d8110 p = 1 ↔ count7 p ≤ 5 := by
  have shape : d8110 p = (if p 160 then d8109 p else d8104 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_0 (p : Pattern) : d8141 p = 1 ↔ count6 p ≤ 0 := by
  have shape : d8141 p = (if p 141 then d0 p else d8135 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_6_1 (p : Pattern) : d8136 p = 1 ↔ count6 p ≤ 1 := by
  have shape : d8136 p = (if p 141 then d8135 p else d8130 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_2 (p : Pattern) : d8131 p = 1 ↔ count6 p ≤ 2 := by
  have shape : d8131 p = (if p 141 then d8130 p else d8125 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_3 (p : Pattern) : d8126 p = 1 ↔ count6 p ≤ 3 := by
  have shape : d8126 p = (if p 141 then d8125 p else d8120 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_4 (p : Pattern) : d8121 p = 1 ↔ count6 p ≤ 4 := by
  have shape : d8121 p = (if p 141 then d8120 p else d8115 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_5 (p : Pattern) : d8116 p = 1 ↔ count6 p ≤ 5 := by
  have shape : d8116 p = (if p 141 then d8115 p else d8110 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_0 (p : Pattern) : d8147 p = 1 ↔ count5 p ≤ 0 := by
  have shape : d8147 p = (if p 138 then d0 p else d8141 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_5_1 (p : Pattern) : d8142 p = 1 ↔ count5 p ≤ 1 := by
  have shape : d8142 p = (if p 138 then d8141 p else d8136 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_2 (p : Pattern) : d8137 p = 1 ↔ count5 p ≤ 2 := by
  have shape : d8137 p = (if p 138 then d8136 p else d8131 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_3 (p : Pattern) : d8132 p = 1 ↔ count5 p ≤ 3 := by
  have shape : d8132 p = (if p 138 then d8131 p else d8126 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_4 (p : Pattern) : d8127 p = 1 ↔ count5 p ≤ 4 := by
  have shape : d8127 p = (if p 138 then d8126 p else d8121 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_5 (p : Pattern) : d8122 p = 1 ↔ count5 p ≤ 5 := by
  have shape : d8122 p = (if p 138 then d8121 p else d8116 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_1 (p : Pattern) : d8148 p = 1 ↔ count4 p ≤ 1 := by
  have shape : d8148 p = (if p 116 then d8147 p else d8142 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_2 (p : Pattern) : d8143 p = 1 ↔ count4 p ≤ 2 := by
  have shape : d8143 p = (if p 116 then d8142 p else d8137 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_3 (p : Pattern) : d8138 p = 1 ↔ count4 p ≤ 3 := by
  have shape : d8138 p = (if p 116 then d8137 p else d8132 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_4 (p : Pattern) : d8133 p = 1 ↔ count4 p ≤ 4 := by
  have shape : d8133 p = (if p 116 then d8132 p else d8127 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_5 (p : Pattern) : d8128 p = 1 ↔ count4 p ≤ 5 := by
  have shape : d8128 p = (if p 116 then d8127 p else d8122 p) := by rfl
  rw [shape]
  cases selected : p 116 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_2 (p : Pattern) : d8149 p = 1 ↔ count3 p ≤ 2 := by
  have shape : d8149 p = (if p 115 then d8148 p else d8143 p) := by rfl
  rw [shape]
  cases selected : p 115 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_3 (p : Pattern) : d8144 p = 1 ↔ count3 p ≤ 3 := by
  have shape : d8144 p = (if p 115 then d8143 p else d8138 p) := by rfl
  rw [shape]
  cases selected : p 115 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_4 (p : Pattern) : d8139 p = 1 ↔ count3 p ≤ 4 := by
  have shape : d8139 p = (if p 115 then d8138 p else d8133 p) := by rfl
  rw [shape]
  cases selected : p 115 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_5 (p : Pattern) : d8134 p = 1 ↔ count3 p ≤ 5 := by
  have shape : d8134 p = (if p 115 then d8133 p else d8128 p) := by rfl
  rw [shape]
  cases selected : p 115 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_2_3 (p : Pattern) : d8150 p = 1 ↔ count2 p ≤ 3 := by
  have shape : d8150 p = (if p 71 then d8149 p else d8144 p) := by rfl
  rw [shape]
  cases selected : p 71 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    have h := budget_3_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_2_4 (p : Pattern) : d8145 p = 1 ↔ count2 p ≤ 4 := by
  have shape : d8145 p = (if p 71 then d8144 p else d8139 p) := by rfl
  rw [shape]
  cases selected : p 71 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    have h := budget_3_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_2_5 (p : Pattern) : d8140 p = 1 ↔ count2 p ≤ 5 := by
  have shape : d8140 p = (if p 71 then d8139 p else d8134 p) := by rfl
  rw [shape]
  cases selected : p 71 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    have h := budget_3_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_1_4 (p : Pattern) : d8151 p = 1 ↔ count1 p ≤ 4 := by
  have shape : d8151 p = (if p 49 then d8150 p else d8145 p) := by rfl
  rw [shape]
  cases selected : p 49 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count1, Nat.zero_add] using budget_2_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count1]
    have h := budget_2_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_1_5 (p : Pattern) : d8146 p = 1 ↔ count1 p ≤ 5 := by
  have shape : d8146 p = (if p 49 then d8145 p else d8140 p) := by rfl
  rw [shape]
  cases selected : p 49 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count1, Nat.zero_add] using budget_2_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count1]
    have h := budget_2_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_0_5 (p : Pattern) : d8152 p = 1 ↔ count0 p ≤ 5 := by
  have shape : d8152 p = (if p 48 then d8151 p else d8146 p) := by rfl
  rw [shape]
  cases selected : p 48 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count0, Nat.zero_add] using budget_1_5 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count0]
    have h := budget_1_4 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
end NetHack.Sokoban22Refined85
