/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.GoalDebts
import NetHack.Sokoban22Refined85.Comparisons355
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem root0_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d0 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare34317 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root516_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d516 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare35866 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root4036_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d4036 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare38097 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root709_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d709 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare38333 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root2183_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d2183 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare39935 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root2502_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d2502 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare41375 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root267_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d267 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare41539 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root652_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d652 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare41771 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root2894_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d2894 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare43530 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root1681_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d1681 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare44338 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root3539_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d3539 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare46021 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root789_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d789 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare46219 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root3224_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d3224 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare47676 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root1503_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d1503 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare48288 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root481_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d481 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare48306 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root484_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d484 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare48313 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root488_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d488 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare48321 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root498_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d498 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare48340 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root948_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d948 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare48723 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root1398_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d1398 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare49334 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root312_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d312 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare49342 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root1150_goal (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    d1150 p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) := by
  have guard : d8152 p = 1 := (budget_0_5 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare49823 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem goal (player : Cell) (p : Pattern) (budget : (support.filter p).length ≤ 5) :
    bonus player p ≤ weightSum (fun c => -Generated.soko2_2Potential.boulder c) (support.filter p) :=
  upper_ite (([25, 45, 46, 47, 67, 69, 70, 89, 90, 91, 111, 113, 114, 133, 134, 135, 136, 155, 156, 157, 158, 159, 177, 180, 181, 199, 200, 201, 202, 223, 245] : List Cell).contains player) (root267_goal p budget) (upper_ite (([27, 28, 29, 30, 50, 51, 52, 73, 74, 76, 93, 94, 95, 96, 97, 98, 118, 119, 120] : List Cell).contains player) (root312_goal p budget) (upper_ite (([48] : List Cell).contains player) (root481_goal p budget) (upper_ite (([49] : List Cell).contains player) (root484_goal p budget) (upper_ite (([71] : List Cell).contains player) (root488_goal p budget) (upper_ite (([115] : List Cell).contains player) (root498_goal p budget) (upper_ite (([116] : List Cell).contains player) (root516_goal p budget) (upper_ite (([138] : List Cell).contains player) (root652_goal p budget) (upper_ite (([141] : List Cell).contains player) (root709_goal p budget) (upper_ite (([160] : List Cell).contains player) (root789_goal p budget) (upper_ite (([161] : List Cell).contains player) (root948_goal p budget) (upper_ite (([162] : List Cell).contains player) (root1150_goal p budget) (upper_ite (([163] : List Cell).contains player) (root1398_goal p budget) (upper_ite (([164, 184, 185, 186] : List Cell).contains player) (root1503_goal p budget) (upper_ite (([182] : List Cell).contains player) (root1681_goal p budget) (upper_ite (([204] : List Cell).contains player) (root2183_goal p budget) (upper_ite (([224] : List Cell).contains player) (root2502_goal p budget) (upper_ite (([225] : List Cell).contains player) (root2894_goal p budget) (upper_ite (([226, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260] : List Cell).contains player) (root3224_goal p budget) (upper_ite (([246] : List Cell).contains player) (root3539_goal p budget) (upper_ite (([247] : List Cell).contains player) (root4036_goal p budget) (root0_goal p budget)))))))))))))))))))))
end NetHack.Sokoban22Refined85
