/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.GoalDebts
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem root0_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d0 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6338 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root258_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d258 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6451 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root195_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d195 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6492 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root201_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d201 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6540 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root74_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d74 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6552 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root75_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d75 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6554 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root524_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d524 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6627 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root586_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d586 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6735 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root658_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d658 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6854 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root219_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d219 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6864 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root733_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d733 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare6998 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root161_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d161 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare7007 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root356_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d356 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare7044 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root485_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d485 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare7104 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root236_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d236 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare7116 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root430_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d430 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare7209 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root309_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d309 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare7253 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root374_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d374 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare7274 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem root319_goal (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    d319 p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) := by
  have guard : d1343 p = 1 := (budget_0_2 p).mpr (by simpa only [count_occupied] using budget)
  have bound := compare7283 p guard
  rw [debt_0_0] at bound
  rw [debt_occupied]
  simp only [Int.zero_add] at bound
  exact Int.le_trans bound (Int.min_le_right _ _)
theorem goal (player : Cell) (p : Pattern) (budget : (support.filter p).length ≤ 2) :
    bonus player p ≤ weightSum (fun c => -Generated.soko1_2Potential.boulder c) (support.filter p) :=
  upper_ite (([29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 55, 56, 76, 82, 102, 108, 128, 154, 180, 206, 232, 258, 284, 310, 336] : List Cell).contains player) (root75_goal p budget) (upper_ite (([105, 106, 131, 157] : List Cell).contains player) (root161_goal p budget) (upper_ite (([115, 116, 117, 142, 143, 169] : List Cell).contains player) (root195_goal p budget) (upper_ite (([132] : List Cell).contains player) (root201_goal p budget) (upper_ite (([133] : List Cell).contains player) (root219_goal p budget) (upper_ite (([134] : List Cell).contains player) (root74_goal p budget) (upper_ite (([135, 161] : List Cell).contains player) (root236_goal p budget) (upper_ite (([140, 163, 164, 166, 167, 184, 185, 189, 190, 191, 194, 210, 211, 212, 213, 214, 215, 216, 218, 219, 220, 236, 237, 238, 239, 241, 242, 244, 245, 246, 262, 263, 264, 265, 270, 272, 288, 289, 290, 291, 292, 293, 294, 296, 297, 317, 318, 319, 320, 322, 345, 348, 370, 371, 372, 373, 374, 396, 397, 399, 400] : List Cell).contains player) (root258_goal p budget) (upper_ite (([141] : List Cell).contains player) (root309_goal p budget) (upper_ite (([158] : List Cell).contains player) (root319_goal p budget) (upper_ite (([159] : List Cell).contains player) (root356_goal p budget) (upper_ite (([160] : List Cell).contains player) (root374_goal p budget) (upper_ite (([168] : List Cell).contains player) (root430_goal p budget) (upper_ite (([186] : List Cell).contains player) (root485_goal p budget) (upper_ite (([187] : List Cell).contains player) (root524_goal p budget) (upper_ite (([192] : List Cell).contains player) (root586_goal p budget) (upper_ite (([193] : List Cell).contains player) (root658_goal p budget) (upper_ite (([271] : List Cell).contains player) (root733_goal p budget) (root0_goal p budget))))))))))))))))))
end NetHack.Sokoban12CostPartition
