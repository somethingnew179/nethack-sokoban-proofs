/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.GoalExpressions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem budget_14_0 (p : Pattern) : d1 p = 1 ↔ count14 p ≤ 0 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 0)
  decide
theorem budget_14_1 (p : Pattern) : d1 p = 1 ↔ count14 p ≤ 1 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 1)
  decide
theorem budget_14_2 (p : Pattern) : d1 p = 1 ↔ count14 p ≤ 2 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 2)
  decide
theorem budget_14_3 (p : Pattern) : d1 p = 1 ↔ count14 p ≤ 3 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 3)
  decide
theorem budget_14_4 (p : Pattern) : d1 p = 1 ↔ count14 p ≤ 4 := by
  change ((1 : Int) = 1 ↔ 0 ≤ 4)
  decide
theorem budget_13_0 (p : Pattern) : d985 p = 1 ↔ count13 p ≤ 0 := by
  have shape : d985 p = (if p 161 then d0 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_13_1 (p : Pattern) : d1 p = 1 ↔ count13 p ≤ 1 := by
  have shape : d1 p = (if p 161 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_2 (p : Pattern) : d1 p = 1 ↔ count13 p ≤ 2 := by
  have shape : d1 p = (if p 161 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_3 (p : Pattern) : d1 p = 1 ↔ count13 p ≤ 3 := by
  have shape : d1 p = (if p 161 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_4 (p : Pattern) : d1 p = 1 ↔ count13 p ≤ 4 := by
  have shape : d1 p = (if p 161 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 161 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_0 (p : Pattern) : d1293 p = 1 ↔ count12 p ≤ 0 := by
  have shape : d1293 p = (if p 160 then d0 p else d985 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_12_1 (p : Pattern) : d1943 p = 1 ↔ count12 p ≤ 1 := by
  have shape : d1943 p = (if p 160 then d985 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_2 (p : Pattern) : d1 p = 1 ↔ count12 p ≤ 2 := by
  have shape : d1 p = (if p 160 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_3 (p : Pattern) : d1 p = 1 ↔ count12 p ≤ 3 := by
  have shape : d1 p = (if p 160 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_4 (p : Pattern) : d1 p = 1 ↔ count12 p ≤ 4 := by
  have shape : d1 p = (if p 160 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_0 (p : Pattern) : d1951 p = 1 ↔ count11 p ≤ 0 := by
  have shape : d1951 p = (if p 159 then d0 p else d1293 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_11_1 (p : Pattern) : d1947 p = 1 ↔ count11 p ≤ 1 := by
  have shape : d1947 p = (if p 159 then d1293 p else d1943 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_2 (p : Pattern) : d1944 p = 1 ↔ count11 p ≤ 2 := by
  have shape : d1944 p = (if p 159 then d1943 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_3 (p : Pattern) : d1 p = 1 ↔ count11 p ≤ 3 := by
  have shape : d1 p = (if p 159 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_4 (p : Pattern) : d1 p = 1 ↔ count11 p ≤ 4 := by
  have shape : d1 p = (if p 159 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_0 (p : Pattern) : d1956 p = 1 ↔ count10 p ≤ 0 := by
  have shape : d1956 p = (if p 158 then d0 p else d1951 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_10_1 (p : Pattern) : d1952 p = 1 ↔ count10 p ≤ 1 := by
  have shape : d1952 p = (if p 158 then d1951 p else d1947 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_2 (p : Pattern) : d1948 p = 1 ↔ count10 p ≤ 2 := by
  have shape : d1948 p = (if p 158 then d1947 p else d1944 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_3 (p : Pattern) : d1945 p = 1 ↔ count10 p ≤ 3 := by
  have shape : d1945 p = (if p 158 then d1944 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_4 (p : Pattern) : d1 p = 1 ↔ count10 p ≤ 4 := by
  have shape : d1 p = (if p 158 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_0 (p : Pattern) : d1961 p = 1 ↔ count9 p ≤ 0 := by
  have shape : d1961 p = (if p 139 then d0 p else d1956 p) := by rfl
  rw [shape]
  cases selected : p 139 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_9_1 (p : Pattern) : d1957 p = 1 ↔ count9 p ≤ 1 := by
  have shape : d1957 p = (if p 139 then d1956 p else d1952 p) := by rfl
  rw [shape]
  cases selected : p 139 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_2 (p : Pattern) : d1953 p = 1 ↔ count9 p ≤ 2 := by
  have shape : d1953 p = (if p 139 then d1952 p else d1948 p) := by rfl
  rw [shape]
  cases selected : p 139 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_3 (p : Pattern) : d1949 p = 1 ↔ count9 p ≤ 3 := by
  have shape : d1949 p = (if p 139 then d1948 p else d1945 p) := by rfl
  rw [shape]
  cases selected : p 139 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_4 (p : Pattern) : d1946 p = 1 ↔ count9 p ≤ 4 := by
  have shape : d1946 p = (if p 139 then d1945 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 139 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_0 (p : Pattern) : d1966 p = 1 ↔ count8 p ≤ 0 := by
  have shape : d1966 p = (if p 138 then d0 p else d1961 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_8_1 (p : Pattern) : d1962 p = 1 ↔ count8 p ≤ 1 := by
  have shape : d1962 p = (if p 138 then d1961 p else d1957 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_2 (p : Pattern) : d1958 p = 1 ↔ count8 p ≤ 2 := by
  have shape : d1958 p = (if p 138 then d1957 p else d1953 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_3 (p : Pattern) : d1954 p = 1 ↔ count8 p ≤ 3 := by
  have shape : d1954 p = (if p 138 then d1953 p else d1949 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_4 (p : Pattern) : d1950 p = 1 ↔ count8 p ≤ 4 := by
  have shape : d1950 p = (if p 138 then d1949 p else d1946 p) := by rfl
  rw [shape]
  cases selected : p 138 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_0 (p : Pattern) : d1971 p = 1 ↔ count7 p ≤ 0 := by
  have shape : d1971 p = (if p 134 then d0 p else d1966 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_7_1 (p : Pattern) : d1967 p = 1 ↔ count7 p ≤ 1 := by
  have shape : d1967 p = (if p 134 then d1966 p else d1962 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_2 (p : Pattern) : d1963 p = 1 ↔ count7 p ≤ 2 := by
  have shape : d1963 p = (if p 134 then d1962 p else d1958 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_3 (p : Pattern) : d1959 p = 1 ↔ count7 p ≤ 3 := by
  have shape : d1959 p = (if p 134 then d1958 p else d1954 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_4 (p : Pattern) : d1955 p = 1 ↔ count7 p ≤ 4 := by
  have shape : d1955 p = (if p 134 then d1954 p else d1950 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    have h := budget_8_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_0 (p : Pattern) : d1976 p = 1 ↔ count6 p ≤ 0 := by
  have shape : d1976 p = (if p 133 then d0 p else d1971 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_6_1 (p : Pattern) : d1972 p = 1 ↔ count6 p ≤ 1 := by
  have shape : d1972 p = (if p 133 then d1971 p else d1967 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_2 (p : Pattern) : d1968 p = 1 ↔ count6 p ≤ 2 := by
  have shape : d1968 p = (if p 133 then d1967 p else d1963 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_3 (p : Pattern) : d1964 p = 1 ↔ count6 p ≤ 3 := by
  have shape : d1964 p = (if p 133 then d1963 p else d1959 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_4 (p : Pattern) : d1960 p = 1 ↔ count6 p ≤ 4 := by
  have shape : d1960 p = (if p 133 then d1959 p else d1955 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_0 (p : Pattern) : d1981 p = 1 ↔ count5 p ≤ 0 := by
  have shape : d1981 p = (if p 132 then d0 p else d1976 p) := by rfl
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_5_1 (p : Pattern) : d1977 p = 1 ↔ count5 p ≤ 1 := by
  have shape : d1977 p = (if p 132 then d1976 p else d1972 p) := by rfl
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_2 (p : Pattern) : d1973 p = 1 ↔ count5 p ≤ 2 := by
  have shape : d1973 p = (if p 132 then d1972 p else d1968 p) := by rfl
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_3 (p : Pattern) : d1969 p = 1 ↔ count5 p ≤ 3 := by
  have shape : d1969 p = (if p 132 then d1968 p else d1964 p) := by rfl
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_4 (p : Pattern) : d1965 p = 1 ↔ count5 p ≤ 4 := by
  have shape : d1965 p = (if p 132 then d1964 p else d1960 p) := by rfl
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_0 (p : Pattern) : d1986 p = 1 ↔ count4 p ≤ 0 := by
  have shape : d1986 p = (if p 113 then d0 p else d1981 p) := by rfl
  rw [shape]
  cases selected : p 113 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_4_1 (p : Pattern) : d1982 p = 1 ↔ count4 p ≤ 1 := by
  have shape : d1982 p = (if p 113 then d1981 p else d1977 p) := by rfl
  rw [shape]
  cases selected : p 113 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_2 (p : Pattern) : d1978 p = 1 ↔ count4 p ≤ 2 := by
  have shape : d1978 p = (if p 113 then d1977 p else d1973 p) := by rfl
  rw [shape]
  cases selected : p 113 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_3 (p : Pattern) : d1974 p = 1 ↔ count4 p ≤ 3 := by
  have shape : d1974 p = (if p 113 then d1973 p else d1969 p) := by rfl
  rw [shape]
  cases selected : p 113 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_4 (p : Pattern) : d1970 p = 1 ↔ count4 p ≤ 4 := by
  have shape : d1970 p = (if p 113 then d1969 p else d1965 p) := by rfl
  rw [shape]
  cases selected : p 113 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_1 (p : Pattern) : d1987 p = 1 ↔ count3 p ≤ 1 := by
  have shape : d1987 p = (if p 112 then d1986 p else d1982 p) := by rfl
  rw [shape]
  cases selected : p 112 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_2 (p : Pattern) : d1983 p = 1 ↔ count3 p ≤ 2 := by
  have shape : d1983 p = (if p 112 then d1982 p else d1978 p) := by rfl
  rw [shape]
  cases selected : p 112 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_3 (p : Pattern) : d1979 p = 1 ↔ count3 p ≤ 3 := by
  have shape : d1979 p = (if p 112 then d1978 p else d1974 p) := by rfl
  rw [shape]
  cases selected : p 112 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_4 (p : Pattern) : d1975 p = 1 ↔ count3 p ≤ 4 := by
  have shape : d1975 p = (if p 112 then d1974 p else d1970 p) := by rfl
  rw [shape]
  cases selected : p 112 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_2_2 (p : Pattern) : d1988 p = 1 ↔ count2 p ≤ 2 := by
  have shape : d1988 p = (if p 106 then d1987 p else d1983 p) := by rfl
  rw [shape]
  cases selected : p 106 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    have h := budget_3_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_2_3 (p : Pattern) : d1984 p = 1 ↔ count2 p ≤ 3 := by
  have shape : d1984 p = (if p 106 then d1983 p else d1979 p) := by rfl
  rw [shape]
  cases selected : p 106 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    have h := budget_3_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_2_4 (p : Pattern) : d1980 p = 1 ↔ count2 p ≤ 4 := by
  have shape : d1980 p = (if p 106 then d1979 p else d1975 p) := by rfl
  rw [shape]
  cases selected : p 106 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    have h := budget_3_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_1_3 (p : Pattern) : d1989 p = 1 ↔ count1 p ≤ 3 := by
  have shape : d1989 p = (if p 86 then d1988 p else d1984 p) := by rfl
  rw [shape]
  cases selected : p 86 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count1, Nat.zero_add] using budget_2_3 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count1]
    have h := budget_2_2 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_1_4 (p : Pattern) : d1985 p = 1 ↔ count1 p ≤ 4 := by
  have shape : d1985 p = (if p 86 then d1984 p else d1980 p) := by rfl
  rw [shape]
  cases selected : p 86 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count1, Nat.zero_add] using budget_2_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count1]
    have h := budget_2_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_0_4 (p : Pattern) : d1990 p = 1 ↔ count0 p ≤ 4 := by
  have shape : d1990 p = (if p 80 then d1989 p else d1985 p) := by rfl
  rw [shape]
  cases selected : p 80 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count0, Nat.zero_add] using budget_1_4 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count0]
    have h := budget_1_3 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
end NetHack.Sokoban32Refined
