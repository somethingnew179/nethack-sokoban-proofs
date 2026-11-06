/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def count14 (_p : Pattern) : Nat := 0
def debt14 (_p : Pattern) : Int := 0
theorem debt_nonnegative14 (p : Pattern) : 0 ≤ debt14 p := by change (0 : Int) ≤ 0; decide
def count13 (p : Pattern) : Nat := (if p 271 then 1 else 0) + count14 p
def debt13 (p : Pattern) : Int := (if p 271 then 0 else 0) + debt14 p
theorem debt_nonnegative13 (p : Pattern) : 0 ≤ debt13 p :=
  Int.add_nonneg (by cases h : p 271 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative14 p)
theorem weight13 : -Generated.soko1_2Potential.boulder 271 = (0 : Int) := by decide
def count12 (p : Pattern) : Nat := (if p 193 then 1 else 0) + count13 p
def debt12 (p : Pattern) : Int := (if p 193 then 2 else 0) + debt13 p
theorem debt_nonnegative12 (p : Pattern) : 0 ≤ debt12 p :=
  Int.add_nonneg (by cases h : p 193 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative13 p)
theorem weight12 : -Generated.soko1_2Potential.boulder 193 = (2 : Int) := by decide
def count11 (p : Pattern) : Nat := (if p 192 then 1 else 0) + count12 p
def debt11 (p : Pattern) : Int := (if p 192 then 3 else 0) + debt12 p
theorem debt_nonnegative11 (p : Pattern) : 0 ≤ debt11 p :=
  Int.add_nonneg (by cases h : p 192 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative12 p)
theorem weight11 : -Generated.soko1_2Potential.boulder 192 = (3 : Int) := by decide
def count10 (p : Pattern) : Nat := (if p 187 then 1 else 0) + count11 p
def debt10 (p : Pattern) : Int := (if p 187 then 8 else 0) + debt11 p
theorem debt_nonnegative10 (p : Pattern) : 0 ≤ debt10 p :=
  Int.add_nonneg (by cases h : p 187 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative11 p)
theorem weight10 : -Generated.soko1_2Potential.boulder 187 = (8 : Int) := by decide
def count9 (p : Pattern) : Nat := (if p 186 then 1 else 0) + count10 p
def debt9 (p : Pattern) : Int := (if p 186 then 11 else 0) + debt10 p
theorem debt_nonnegative9 (p : Pattern) : 0 ≤ debt9 p :=
  Int.add_nonneg (by cases h : p 186 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative10 p)
theorem weight9 : -Generated.soko1_2Potential.boulder 186 = (11 : Int) := by decide
def count8 (p : Pattern) : Nat := (if p 168 then 1 else 0) + count9 p
def debt8 (p : Pattern) : Int := (if p 168 then 0 else 0) + debt9 p
theorem debt_nonnegative8 (p : Pattern) : 0 ≤ debt8 p :=
  Int.add_nonneg (by cases h : p 168 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative9 p)
theorem weight8 : -Generated.soko1_2Potential.boulder 168 = (0 : Int) := by decide
def count7 (p : Pattern) : Nat := (if p 160 then 1 else 0) + count8 p
def debt7 (p : Pattern) : Int := (if p 160 then 12 else 0) + debt8 p
theorem debt_nonnegative7 (p : Pattern) : 0 ≤ debt7 p :=
  Int.add_nonneg (by cases h : p 160 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative8 p)
theorem weight7 : -Generated.soko1_2Potential.boulder 160 = (12 : Int) := by decide
def count6 (p : Pattern) : Nat := (if p 159 then 1 else 0) + count7 p
def debt6 (p : Pattern) : Int := (if p 159 then 11 else 0) + debt7 p
theorem debt_nonnegative6 (p : Pattern) : 0 ≤ debt6 p :=
  Int.add_nonneg (by cases h : p 159 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative7 p)
theorem weight6 : -Generated.soko1_2Potential.boulder 159 = (11 : Int) := by decide
def count5 (p : Pattern) : Nat := (if p 158 then 1 else 0) + count6 p
def debt5 (p : Pattern) : Int := (if p 158 then 10 else 0) + debt6 p
theorem debt_nonnegative5 (p : Pattern) : 0 ≤ debt5 p :=
  Int.add_nonneg (by cases h : p 158 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative6 p)
theorem weight5 : -Generated.soko1_2Potential.boulder 158 = (10 : Int) := by decide
def count4 (p : Pattern) : Nat := (if p 141 then 1 else 0) + count5 p
def debt4 (p : Pattern) : Int := (if p 141 then 0 else 0) + debt5 p
theorem debt_nonnegative4 (p : Pattern) : 0 ≤ debt4 p :=
  Int.add_nonneg (by cases h : p 141 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative5 p)
theorem weight4 : -Generated.soko1_2Potential.boulder 141 = (0 : Int) := by decide
def count3 (p : Pattern) : Nat := (if p 134 then 1 else 0) + count4 p
def debt3 (p : Pattern) : Int := (if p 134 then 13 else 0) + debt4 p
theorem debt_nonnegative3 (p : Pattern) : 0 ≤ debt3 p :=
  Int.add_nonneg (by cases h : p 134 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative4 p)
theorem weight3 : -Generated.soko1_2Potential.boulder 134 = (13 : Int) := by decide
def count2 (p : Pattern) : Nat := (if p 133 then 1 else 0) + count3 p
def debt2 (p : Pattern) : Int := (if p 133 then 12 else 0) + debt3 p
theorem debt_nonnegative2 (p : Pattern) : 0 ≤ debt2 p :=
  Int.add_nonneg (by cases h : p 133 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative3 p)
theorem weight2 : -Generated.soko1_2Potential.boulder 133 = (12 : Int) := by decide
def count1 (p : Pattern) : Nat := (if p 132 then 1 else 0) + count2 p
def debt1 (p : Pattern) : Int := (if p 132 then 11 else 0) + debt2 p
theorem debt_nonnegative1 (p : Pattern) : 0 ≤ debt1 p :=
  Int.add_nonneg (by cases h : p 132 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative2 p)
theorem weight1 : -Generated.soko1_2Potential.boulder 132 = (11 : Int) := by decide
def count0 (p : Pattern) : Nat := (if p 108 then 1 else 0) + count1 p
def debt0 (p : Pattern) : Int := (if p 108 then 14 else 0) + debt1 p
theorem debt_nonnegative0 (p : Pattern) : 0 ≤ debt0 p :=
  Int.add_nonneg (by cases h : p 108 <;> (try simp only [h, ↓reduceIte]) <;> decide) (debt_nonnegative1 p)
theorem weight0 : -Generated.soko1_2Potential.boulder 108 = (14 : Int) := by decide
theorem count_occupied (p : Pattern) : (support.filter p).length = count0 p := by
  unfold support
  simp only [count_filter_cons, List.filter_nil, List.length_nil]
  rfl
theorem debt_occupied (p : Pattern) : weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) = debt0 p := by
  unfold support
  simp only [sum_filter_cons, List.filter_nil, weightSum]
  rw [weight0, weight1, weight2, weight3, weight4, weight5, weight6, weight7, weight8, weight9, weight10, weight11, weight12, weight13]
  rfl
end NetHack.Sokoban12CostPartition
