/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Roots
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def count17 (_p : Pattern) : Nat := 0
def debt17 (_p : Pattern) : Int := 0
theorem debt_nonnegative17 (p : Pattern) : 0 ≤ debt17 p := by change (0 : Int) ≤ 0; decide
def count16 (p : Pattern) : Nat := (if p 247 then 1 else 0) + count17 p
def debt16 (p : Pattern) : Int := (if p 247 then 9 else 0) + debt17 p
theorem debt_nonnegative16 (p : Pattern) : 0 ≤ debt16 p :=
  Int.add_nonneg (by cases h : p 247 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative17 p)
theorem weight16 : -Generated.soko2_2Potential.boulder 247 = (9 : Int) := by decide
def count15 (p : Pattern) : Nat := (if p 246 then 1 else 0) + count16 p
def debt15 (p : Pattern) : Int := (if p 246 then 8 else 0) + debt16 p
theorem debt_nonnegative15 (p : Pattern) : 0 ≤ debt15 p :=
  Int.add_nonneg (by cases h : p 246 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative16 p)
theorem weight15 : -Generated.soko2_2Potential.boulder 246 = (8 : Int) := by decide
def count14 (p : Pattern) : Nat := (if p 225 then 1 else 0) + count15 p
def debt14 (p : Pattern) : Int := (if p 225 then 8 else 0) + debt15 p
theorem debt_nonnegative14 (p : Pattern) : 0 ≤ debt14 p :=
  Int.add_nonneg (by cases h : p 225 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative15 p)
theorem weight14 : -Generated.soko2_2Potential.boulder 225 = (8 : Int) := by decide
def count13 (p : Pattern) : Nat := (if p 224 then 1 else 0) + count14 p
def debt13 (p : Pattern) : Int := (if p 224 then 7 else 0) + debt14 p
theorem debt_nonnegative13 (p : Pattern) : 0 ≤ debt13 p :=
  Int.add_nonneg (by cases h : p 224 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative14 p)
theorem weight13 : -Generated.soko2_2Potential.boulder 224 = (7 : Int) := by decide
def count12 (p : Pattern) : Nat := (if p 204 then 1 else 0) + count13 p
def debt12 (p : Pattern) : Int := (if p 204 then 8 else 0) + debt13 p
theorem debt_nonnegative12 (p : Pattern) : 0 ≤ debt12 p :=
  Int.add_nonneg (by cases h : p 204 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative13 p)
theorem weight12 : -Generated.soko2_2Potential.boulder 204 = (8 : Int) := by decide
def count11 (p : Pattern) : Nat := (if p 182 then 1 else 0) + count12 p
def debt11 (p : Pattern) : Int := (if p 182 then 7 else 0) + debt12 p
theorem debt_nonnegative11 (p : Pattern) : 0 ≤ debt11 p :=
  Int.add_nonneg (by cases h : p 182 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative12 p)
theorem weight11 : -Generated.soko2_2Potential.boulder 182 = (7 : Int) := by decide
def count10 (p : Pattern) : Nat := (if p 163 then 1 else 0) + count11 p
def debt10 (p : Pattern) : Int := (if p 163 then 3 else 0) + debt11 p
theorem debt_nonnegative10 (p : Pattern) : 0 ≤ debt10 p :=
  Int.add_nonneg (by cases h : p 163 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative11 p)
theorem weight10 : -Generated.soko2_2Potential.boulder 163 = (3 : Int) := by decide
def count9 (p : Pattern) : Nat := (if p 162 then 1 else 0) + count10 p
def debt9 (p : Pattern) : Int := (if p 162 then 4 else 0) + debt10 p
theorem debt_nonnegative9 (p : Pattern) : 0 ≤ debt9 p :=
  Int.add_nonneg (by cases h : p 162 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative10 p)
theorem weight9 : -Generated.soko2_2Potential.boulder 162 = (4 : Int) := by decide
def count8 (p : Pattern) : Nat := (if p 161 then 1 else 0) + count9 p
def debt8 (p : Pattern) : Int := (if p 161 then 5 else 0) + debt9 p
theorem debt_nonnegative8 (p : Pattern) : 0 ≤ debt8 p :=
  Int.add_nonneg (by cases h : p 161 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative9 p)
theorem weight8 : -Generated.soko2_2Potential.boulder 161 = (5 : Int) := by decide
def count7 (p : Pattern) : Nat := (if p 160 then 1 else 0) + count8 p
def debt7 (p : Pattern) : Int := (if p 160 then 6 else 0) + debt8 p
theorem debt_nonnegative7 (p : Pattern) : 0 ≤ debt7 p :=
  Int.add_nonneg (by cases h : p 160 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative8 p)
theorem weight7 : -Generated.soko2_2Potential.boulder 160 = (6 : Int) := by decide
def count6 (p : Pattern) : Nat := (if p 141 then 1 else 0) + count7 p
def debt6 (p : Pattern) : Int := (if p 141 then 2 else 0) + debt7 p
theorem debt_nonnegative6 (p : Pattern) : 0 ≤ debt6 p :=
  Int.add_nonneg (by cases h : p 141 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative7 p)
theorem weight6 : -Generated.soko2_2Potential.boulder 141 = (2 : Int) := by decide
def count5 (p : Pattern) : Nat := (if p 138 then 1 else 0) + count6 p
def debt5 (p : Pattern) : Int := (if p 138 then 5 else 0) + debt6 p
theorem debt_nonnegative5 (p : Pattern) : 0 ≤ debt5 p :=
  Int.add_nonneg (by cases h : p 138 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative6 p)
theorem weight5 : -Generated.soko2_2Potential.boulder 138 = (5 : Int) := by decide
def count4 (p : Pattern) : Nat := (if p 116 then 1 else 0) + count5 p
def debt4 (p : Pattern) : Int := (if p 116 then 4 else 0) + debt5 p
theorem debt_nonnegative4 (p : Pattern) : 0 ≤ debt4 p :=
  Int.add_nonneg (by cases h : p 116 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative5 p)
theorem weight4 : -Generated.soko2_2Potential.boulder 116 = (4 : Int) := by decide
def count3 (p : Pattern) : Nat := (if p 115 then 1 else 0) + count4 p
def debt3 (p : Pattern) : Int := (if p 115 then 3 else 0) + debt4 p
theorem debt_nonnegative3 (p : Pattern) : 0 ≤ debt3 p :=
  Int.add_nonneg (by cases h : p 115 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative4 p)
theorem weight3 : -Generated.soko2_2Potential.boulder 115 = (3 : Int) := by decide
def count2 (p : Pattern) : Nat := (if p 71 then 1 else 0) + count3 p
def debt2 (p : Pattern) : Int := (if p 71 then 1 else 0) + debt3 p
theorem debt_nonnegative2 (p : Pattern) : 0 ≤ debt2 p :=
  Int.add_nonneg (by cases h : p 71 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative3 p)
theorem weight2 : -Generated.soko2_2Potential.boulder 71 = (1 : Int) := by decide
def count1 (p : Pattern) : Nat := (if p 49 then 1 else 0) + count2 p
def debt1 (p : Pattern) : Int := (if p 49 then 0 else 0) + debt2 p
theorem debt_nonnegative1 (p : Pattern) : 0 ≤ debt1 p :=
  Int.add_nonneg (by cases h : p 49 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative2 p)
theorem weight1 : -Generated.soko2_2Potential.boulder 49 = (0 : Int) := by decide
def count0 (p : Pattern) : Nat := (if p 48 then 1 else 0) + count1 p
def debt0 (p : Pattern) : Int := (if p 48 then 0 else 0) + debt1 p
theorem debt_nonnegative0 (p : Pattern) : 0 ≤ debt0 p :=
  Int.add_nonneg (by cases h : p 48 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative1 p)
theorem weight0 : -Generated.soko2_2Potential.boulder 48 = (0 : Int) := by decide
theorem count_occupied (p : Pattern) : (support.filter p).length = count0 p := by
  unfold support
  simp only [count_filter_cons, List.filter_nil, List.length_nil]
  rfl
theorem debt_occupied (p : Pattern) : weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) = debt0 p := by
  unfold support
  simp only [sum_filter_cons, List.filter_nil, weightSum]
  rw [weight0, weight1, weight2, weight3, weight4, weight5, weight6, weight7, weight8, weight9, weight10, weight11, weight12, weight13, weight14, weight15, weight16]
  rfl
end NetHack.Sokoban22Refined85
