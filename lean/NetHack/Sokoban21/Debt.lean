/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.Projection
namespace NetHack.Sokoban21
open NetHack.Sokoban.LowerBounds
def patternDebt (pattern : Twelve) : Int := (if pattern.a then (15 : Int) else 0) + ((if pattern.b then (15 : Int) else 0) + ((if pattern.c then (3 : Int) else 0) + ((if pattern.d then (2 : Int) else 0) + ((if pattern.e then (0 : Int) else 0) + ((if pattern.f then (0 : Int) else 0) + ((if pattern.g then (15 : Int) else 0) + ((if pattern.h then (0 : Int) else 0) + ((if pattern.i then (1 : Int) else 0) + ((if pattern.j then (2 : Int) else 0) + ((if pattern.k then (0 : Int) else 0) + ((if pattern.l then (0 : Int) else 0) + (0))))))))))))
private theorem filter_weight_cons (weight : NetHack.Sokoban.Cell → Int)
    (predicate : NetHack.Sokoban.Cell → Bool) (cell : NetHack.Sokoban.Cell) (cells : List NetHack.Sokoban.Cell) :
    weightSum weight ((cell :: cells).filter predicate) =
      (if predicate cell then weight cell else 0) + weightSum weight (cells.filter predicate) := by
  cases selected : predicate cell <;> simp [selected, weightSum]
theorem known_support0 (pattern : Twelve) : known pattern 183 = pattern.a := by rfl
theorem debt_support0 : debt 183 = (15 : Int) := by decide
theorem known_support1 (pattern : Twelve) : known pattern 145 = pattern.b := by rfl
theorem debt_support1 : debt 145 = (15 : Int) := by decide
theorem known_support2 (pattern : Twelve) : known pattern 65 = pattern.c := by rfl
theorem debt_support2 : debt 65 = (3 : Int) := by decide
theorem known_support3 (pattern : Twelve) : known pattern 45 = pattern.d := by rfl
theorem debt_support3 : debt 45 = (2 : Int) := by decide
theorem known_support4 (pattern : Twelve) : known pattern 48 = pattern.e := by rfl
theorem debt_support4 : debt 48 = (0 : Int) := by decide
theorem known_support5 (pattern : Twelve) : known pattern 68 = pattern.f := by rfl
theorem debt_support5 : debt 68 = (0 : Int) := by decide
theorem known_support6 (pattern : Twelve) : known pattern 126 = pattern.g := by rfl
theorem debt_support6 : debt 126 = (15 : Int) := by decide
theorem known_support7 (pattern : Twelve) : known pattern 47 = pattern.h := by rfl
theorem debt_support7 : debt 47 = (0 : Int) := by decide
theorem known_support8 (pattern : Twelve) : known pattern 67 = pattern.i := by rfl
theorem debt_support8 : debt 67 = (1 : Int) := by decide
theorem known_support9 (pattern : Twelve) : known pattern 66 = pattern.j := by rfl
theorem debt_support9 : debt 66 = (2 : Int) := by decide
theorem known_support10 (pattern : Twelve) : known pattern 70 = pattern.k := by rfl
theorem debt_support10 : debt 70 = (0 : Int) := by decide
theorem known_support11 (pattern : Twelve) : known pattern 71 = pattern.l := by rfl
theorem debt_support11 : debt 71 = (0 : Int) := by decide
theorem occupied_debt (pattern : Twelve) :
    weightSum debt (Projection.occupied pattern) = patternDebt pattern := by
  unfold Projection.occupied support
  simp only [filter_weight_cons, List.filter_nil, weightSum]
  rw [known_support0, known_support1, known_support2, known_support3, known_support4, known_support5, known_support6, known_support7, known_support8, known_support9, known_support10, known_support11]
  rw [debt_support0, debt_support1, debt_support2, debt_support3, debt_support4, debt_support5, debt_support6, debt_support7, debt_support8, debt_support9, debt_support10, debt_support11]
  rfl
end NetHack.Sokoban21
