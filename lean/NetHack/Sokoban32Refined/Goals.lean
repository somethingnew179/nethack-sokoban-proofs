/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.GoalDebts
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem root0_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d0 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare9481 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root388_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d388 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare9785 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root134_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d134 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare9998 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root327_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d327 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare10076 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root455_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d455 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare10266 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root652_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d652 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare10565 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root537_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d537 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare10746 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root227_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d227 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare10810 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root292_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d292 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare10863 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root742_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d742 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare11112 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root173_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d173 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare11126 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root176_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d176 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare11129 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root183_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d183 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare11136 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root696_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d696 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare11361 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root825_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d825 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare11696 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root255_goal (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    d255 p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) := by
  have guard : d1990 p = 1 := (budget_0_4 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare11724 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem goal (player : Cell) (p : Pattern) (budget : (support.filter p).length ≤ 4) :
    bonus player p ≤ weightSum (fun c => -Generated.soko3_2Potential.boulder c) (support.filter p) :=
  upper_ite (([28, 29, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 79, 88, 105, 108, 109, 110, 114, 131, 135, 136, 137, 157, 162, 163, 165, 166, 183, 188, 189, 192, 209, 210, 211, 212, 213, 214, 215, 216, 218, 235, 239, 241, 242, 243, 244, 245, 261, 262, 263, 265, 266, 267, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 287, 288, 289, 290, 291, 292, 293, 294, 295, 317, 318, 320, 321] : List Cell).contains player) (root134_goal p budget) (upper_ite (([80] : List Cell).contains player) (root173_goal p budget) (upper_ite (([86] : List Cell).contains player) (root176_goal p budget) (upper_ite (([106] : List Cell).contains player) (root183_goal p budget) (upper_ite (([112] : List Cell).contains player) (root227_goal p budget) (upper_ite (([113] : List Cell).contains player) (root255_goal p budget) (upper_ite (([132] : List Cell).contains player) (root292_goal p budget) (upper_ite (([133] : List Cell).contains player) (root327_goal p budget) (upper_ite (([134] : List Cell).contains player) (root388_goal p budget) (upper_ite (([138] : List Cell).contains player) (root455_goal p budget) (upper_ite (([139] : List Cell).contains player) (root537_goal p budget) (upper_ite (([158] : List Cell).contains player) (root652_goal p budget) (upper_ite (([159] : List Cell).contains player) (root696_goal p budget) (upper_ite (([160] : List Cell).contains player) (root742_goal p budget) (upper_ite (([161] : List Cell).contains player) (root825_goal p budget) (root0_goal p budget)))))))))))))))
end NetHack.Sokoban32Refined
