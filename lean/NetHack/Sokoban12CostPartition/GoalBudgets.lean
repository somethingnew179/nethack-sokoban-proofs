/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.GoalExpressions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
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
theorem budget_13_0 (p : Pattern) : d1233 p = 1 ↔ count13 p ≤ 0 := by
  have shape : d1233 p = (if p 271 then d0 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 271 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_13_1 (p : Pattern) : d1 p = 1 ↔ count13 p ≤ 1 := by
  have shape : d1 p = (if p 271 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 271 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_13_2 (p : Pattern) : d1 p = 1 ↔ count13 p ≤ 2 := by
  have shape : d1 p = (if p 271 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 271 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count13, Nat.zero_add] using budget_14_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count13]
    have h := budget_14_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_0 (p : Pattern) : d1311 p = 1 ↔ count12 p ≤ 0 := by
  have shape : d1311 p = (if p 193 then d0 p else d1233 p) := by rfl
  rw [shape]
  cases selected : p 193 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_12_1 (p : Pattern) : d1309 p = 1 ↔ count12 p ≤ 1 := by
  have shape : d1309 p = (if p 193 then d1233 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 193 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_12_2 (p : Pattern) : d1 p = 1 ↔ count12 p ≤ 2 := by
  have shape : d1 p = (if p 193 then d1 p else d1 p) := by simp only [ite_self]
  rw [shape]
  cases selected : p 193 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count12, Nat.zero_add] using budget_13_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count12]
    have h := budget_13_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_0 (p : Pattern) : d1314 p = 1 ↔ count11 p ≤ 0 := by
  have shape : d1314 p = (if p 192 then d0 p else d1311 p) := by rfl
  rw [shape]
  cases selected : p 192 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_11_1 (p : Pattern) : d1312 p = 1 ↔ count11 p ≤ 1 := by
  have shape : d1312 p = (if p 192 then d1311 p else d1309 p) := by rfl
  rw [shape]
  cases selected : p 192 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_11_2 (p : Pattern) : d1310 p = 1 ↔ count11 p ≤ 2 := by
  have shape : d1310 p = (if p 192 then d1309 p else d1 p) := by rfl
  rw [shape]
  cases selected : p 192 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count11, Nat.zero_add] using budget_12_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count11]
    have h := budget_12_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_0 (p : Pattern) : d1317 p = 1 ↔ count10 p ≤ 0 := by
  have shape : d1317 p = (if p 187 then d0 p else d1314 p) := by rfl
  rw [shape]
  cases selected : p 187 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_10_1 (p : Pattern) : d1315 p = 1 ↔ count10 p ≤ 1 := by
  have shape : d1315 p = (if p 187 then d1314 p else d1312 p) := by rfl
  rw [shape]
  cases selected : p 187 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_10_2 (p : Pattern) : d1313 p = 1 ↔ count10 p ≤ 2 := by
  have shape : d1313 p = (if p 187 then d1312 p else d1310 p) := by rfl
  rw [shape]
  cases selected : p 187 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count10, Nat.zero_add] using budget_11_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count10]
    have h := budget_11_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_0 (p : Pattern) : d1320 p = 1 ↔ count9 p ≤ 0 := by
  have shape : d1320 p = (if p 186 then d0 p else d1317 p) := by rfl
  rw [shape]
  cases selected : p 186 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_9_1 (p : Pattern) : d1318 p = 1 ↔ count9 p ≤ 1 := by
  have shape : d1318 p = (if p 186 then d1317 p else d1315 p) := by rfl
  rw [shape]
  cases selected : p 186 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_9_2 (p : Pattern) : d1316 p = 1 ↔ count9 p ≤ 2 := by
  have shape : d1316 p = (if p 186 then d1315 p else d1313 p) := by rfl
  rw [shape]
  cases selected : p 186 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count9, Nat.zero_add] using budget_10_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count9]
    have h := budget_10_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_0 (p : Pattern) : d1323 p = 1 ↔ count8 p ≤ 0 := by
  have shape : d1323 p = (if p 168 then d0 p else d1320 p) := by rfl
  rw [shape]
  cases selected : p 168 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_8_1 (p : Pattern) : d1321 p = 1 ↔ count8 p ≤ 1 := by
  have shape : d1321 p = (if p 168 then d1320 p else d1318 p) := by rfl
  rw [shape]
  cases selected : p 168 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_8_2 (p : Pattern) : d1319 p = 1 ↔ count8 p ≤ 2 := by
  have shape : d1319 p = (if p 168 then d1318 p else d1316 p) := by rfl
  rw [shape]
  cases selected : p 168 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count8, Nat.zero_add] using budget_9_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count8]
    have h := budget_9_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_7_0 (p : Pattern) : d1326 p = 1 ↔ count7 p ≤ 0 := by
  have shape : d1326 p = (if p 160 then d0 p else d1323 p) := by rfl
  rw [shape]
  cases selected : p 160 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count7, Nat.zero_add] using budget_8_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count7]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_7_1 (p : Pattern) : d1324 p = 1 ↔ count7 p ≤ 1 := by
  have shape : d1324 p = (if p 160 then d1323 p else d1321 p) := by rfl
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
theorem budget_7_2 (p : Pattern) : d1322 p = 1 ↔ count7 p ≤ 2 := by
  have shape : d1322 p = (if p 160 then d1321 p else d1319 p) := by rfl
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
theorem budget_6_0 (p : Pattern) : d1329 p = 1 ↔ count6 p ≤ 0 := by
  have shape : d1329 p = (if p 159 then d0 p else d1326 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_6_1 (p : Pattern) : d1327 p = 1 ↔ count6 p ≤ 1 := by
  have shape : d1327 p = (if p 159 then d1326 p else d1324 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_6_2 (p : Pattern) : d1325 p = 1 ↔ count6 p ≤ 2 := by
  have shape : d1325 p = (if p 159 then d1324 p else d1322 p) := by rfl
  rw [shape]
  cases selected : p 159 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count6, Nat.zero_add] using budget_7_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count6]
    have h := budget_7_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_0 (p : Pattern) : d1332 p = 1 ↔ count5 p ≤ 0 := by
  have shape : d1332 p = (if p 158 then d0 p else d1329 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_5_1 (p : Pattern) : d1330 p = 1 ↔ count5 p ≤ 1 := by
  have shape : d1330 p = (if p 158 then d1329 p else d1327 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_5_2 (p : Pattern) : d1328 p = 1 ↔ count5 p ≤ 2 := by
  have shape : d1328 p = (if p 158 then d1327 p else d1325 p) := by rfl
  rw [shape]
  cases selected : p 158 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count5, Nat.zero_add] using budget_6_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count5]
    have h := budget_6_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_0 (p : Pattern) : d1335 p = 1 ↔ count4 p ≤ 0 := by
  have shape : d1335 p = (if p 141 then d0 p else d1332 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_4_1 (p : Pattern) : d1333 p = 1 ↔ count4 p ≤ 1 := by
  have shape : d1333 p = (if p 141 then d1332 p else d1330 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_4_2 (p : Pattern) : d1331 p = 1 ↔ count4 p ≤ 2 := by
  have shape : d1331 p = (if p 141 then d1330 p else d1328 p) := by rfl
  rw [shape]
  cases selected : p 141 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count4, Nat.zero_add] using budget_5_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count4]
    have h := budget_5_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_0 (p : Pattern) : d1338 p = 1 ↔ count3 p ≤ 0 := by
  have shape : d1338 p = (if p 134 then d0 p else d1335 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_3_1 (p : Pattern) : d1336 p = 1 ↔ count3 p ≤ 1 := by
  have shape : d1336 p = (if p 134 then d1335 p else d1333 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_3_2 (p : Pattern) : d1334 p = 1 ↔ count3 p ≤ 2 := by
  have shape : d1334 p = (if p 134 then d1333 p else d1331 p) := by rfl
  rw [shape]
  cases selected : p 134 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count3, Nat.zero_add] using budget_4_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count3]
    have h := budget_4_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_2_0 (p : Pattern) : d1341 p = 1 ↔ count2 p ≤ 0 := by
  have shape : d1341 p = (if p 133 then d0 p else d1338 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_0 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    change ((0 : Int) = 1 ↔ 1 + _ ≤ 0)
    constructor <;> intro h <;> omega
theorem budget_2_1 (p : Pattern) : d1339 p = 1 ↔ count2 p ≤ 1 := by
  have shape : d1339 p = (if p 133 then d1338 p else d1336 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    have h := budget_3_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_2_2 (p : Pattern) : d1337 p = 1 ↔ count2 p ≤ 2 := by
  have shape : d1337 p = (if p 133 then d1336 p else d1334 p) := by rfl
  rw [shape]
  cases selected : p 133 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count2, Nat.zero_add] using budget_3_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count2]
    have h := budget_3_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_1_1 (p : Pattern) : d1342 p = 1 ↔ count1 p ≤ 1 := by
  have shape : d1342 p = (if p 132 then d1341 p else d1339 p) := by rfl
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count1, Nat.zero_add] using budget_2_1 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count1]
    have h := budget_2_0 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_1_2 (p : Pattern) : d1340 p = 1 ↔ count1 p ≤ 2 := by
  have shape : d1340 p = (if p 132 then d1339 p else d1337 p) := by rfl
  rw [shape]
  cases selected : p 132 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count1, Nat.zero_add] using budget_2_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count1]
    have h := budget_2_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
theorem budget_0_2 (p : Pattern) : d1343 p = 1 ↔ count0 p ≤ 2 := by
  have shape : d1343 p = (if p 108 then d1342 p else d1340 p) := by rfl
  rw [shape]
  cases selected : p 108 with
  | false =>
    simpa only [selected, Bool.false_eq_true, ↓reduceIte, count0, Nat.zero_add] using budget_1_2 p
  | true =>
    simp only [selected, Bool.false_eq_true, ↓reduceIte, count0]
    have h := budget_1_1 p
    constructor
    · intro bound; have hh := h.mp bound; omega
    · intro bound; apply h.mpr; omega
end NetHack.Sokoban12CostPartition
