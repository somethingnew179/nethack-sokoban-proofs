import NetHack.Sokoban12CostPartition.Goals
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard0 (p : Pattern) (guard : walkGuard soko1_2.board support p 29 55 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound0 (p : Pattern) (guard : walkGuard soko1_2.board support p 29 55 .south = true) : bonus 29 p ≤ bonus 55 p := by
  have certified := compare0 p (guard0 p guard)
  simpa only [at29, at55, Int.zero_add] using certified
theorem check0 (p : Pattern) : (!walkGuard soko1_2.board support p 29 55 .south || decide (bonus 29 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound0 p)
theorem guard1 (p : Pattern) (guard : walkGuard soko1_2.board support p 29 30 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1 (p : Pattern) (guard : walkGuard soko1_2.board support p 29 30 .east = true) : bonus 29 p ≤ bonus 30 p := by
  have certified := compare0 p (guard1 p guard)
  simpa only [at29, at30, Int.zero_add] using certified
theorem check1 (p : Pattern) : (!walkGuard soko1_2.board support p 29 30 .east || decide (bonus 29 p ≤ bonus 30 p)) = true :=
  check_of_implication _ _ (bound1 p)
theorem guard2 (p : Pattern) (guard : pushGuard support p 29 30 31 50 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound2 (p : Pattern) (guard : pushGuard support p 29 30 31 50 = true) : bonus 29 p ≤ 1 + Generated.soko1_2Potential.boulder 50 - Generated.soko1_2Potential.boulder 30 + bonus 30 (change p 30 (some 50)) := by
  have certified := compare1 p (guard2 p guard)
  change d75 p ≤ (18 : Int) + d75 (change p 30 (some 50))
  have normalized := agree75 _ _ (change_representative support p 30 (some 50) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (18 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check2 (p : Pattern) : (!pushGuard support p 29 30 31 50 || decide (bonus 29 p ≤ 1 + Generated.soko1_2Potential.boulder 50 - Generated.soko1_2Potential.boulder 30 + bonus 30 (change p 30 (some 50)))) = true :=
  check_of_implication _ _ (bound2 p)
theorem guard3 (p : Pattern) (guard : pushGuard support p 29 30 31 32 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound3 (p : Pattern) (guard : pushGuard support p 29 30 31 32 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 32 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard3 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check3 (p : Pattern) : (!pushGuard support p 29 30 31 32 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 32 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound3 p)
theorem guard4 (p : Pattern) (guard : pushGuard support p 29 30 31 33 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound4 (p : Pattern) (guard : pushGuard support p 29 30 31 33 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 33 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard4 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check4 (p : Pattern) : (!pushGuard support p 29 30 31 33 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 33 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound4 p)
theorem guard5 (p : Pattern) (guard : pushGuard support p 29 30 31 34 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound5 (p : Pattern) (guard : pushGuard support p 29 30 31 34 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 34 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard5 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check5 (p : Pattern) : (!pushGuard support p 29 30 31 34 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 34 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound5 p)
theorem guard6 (p : Pattern) (guard : pushGuard support p 29 30 31 35 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound6 (p : Pattern) (guard : pushGuard support p 29 30 31 35 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 35 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard6 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check6 (p : Pattern) : (!pushGuard support p 29 30 31 35 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 35 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound6 p)
theorem guard7 (p : Pattern) (guard : pushGuard support p 29 30 31 36 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound7 (p : Pattern) (guard : pushGuard support p 29 30 31 36 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 36 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard7 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check7 (p : Pattern) : (!pushGuard support p 29 30 31 36 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 36 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound7 p)
theorem guard8 (p : Pattern) (guard : pushGuard support p 29 30 31 37 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound8 (p : Pattern) (guard : pushGuard support p 29 30 31 37 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 37 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard8 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check8 (p : Pattern) : (!pushGuard support p 29 30 31 37 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 37 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound8 p)
theorem guard9 (p : Pattern) (guard : pushGuard support p 29 30 31 38 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound9 (p : Pattern) (guard : pushGuard support p 29 30 31 38 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 38 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard9 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check9 (p : Pattern) : (!pushGuard support p 29 30 31 38 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 38 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound9 p)
theorem guard10 (p : Pattern) (guard : pushGuard support p 29 30 31 39 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound10 (p : Pattern) (guard : pushGuard support p 29 30 31 39 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 39 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard10 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check10 (p : Pattern) : (!pushGuard support p 29 30 31 39 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 39 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound10 p)
theorem guard11 (p : Pattern) (guard : pushGuard support p 29 30 31 40 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound11 (p : Pattern) (guard : pushGuard support p 29 30 31 40 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 40 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard11 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check11 (p : Pattern) : (!pushGuard support p 29 30 31 40 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 40 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound11 p)
theorem guard12 (p : Pattern) (guard : pushGuard support p 29 30 31 41 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound12 (p : Pattern) (guard : pushGuard support p 29 30 31 41 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 41 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard12 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check12 (p : Pattern) : (!pushGuard support p 29 30 31 41 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 41 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound12 p)
theorem guard13 (p : Pattern) (guard : pushGuard support p 29 30 31 42 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound13 (p : Pattern) (guard : pushGuard support p 29 30 31 42 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 42 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard13 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check13 (p : Pattern) : (!pushGuard support p 29 30 31 42 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 42 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound13 p)
theorem guard14 (p : Pattern) (guard : pushGuard support p 29 30 31 43 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound14 (p : Pattern) (guard : pushGuard support p 29 30 31 43 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 43 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard14 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check14 (p : Pattern) : (!pushGuard support p 29 30 31 43 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 43 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound14 p)
theorem guard15 (p : Pattern) (guard : pushGuard support p 29 30 31 44 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound15 (p : Pattern) (guard : pushGuard support p 29 30 31 44 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 44 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard15 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check15 (p : Pattern) : (!pushGuard support p 29 30 31 44 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 44 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound15 p)
theorem guard16 (p : Pattern) (guard : pushGuard support p 29 30 31 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound16 (p : Pattern) (guard : pushGuard support p 29 30 31 45 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 45 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard16 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check16 (p : Pattern) : (!pushGuard support p 29 30 31 45 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 45 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound16 p)
theorem guard17 (p : Pattern) (guard : pushGuard support p 29 30 31 46 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound17 (p : Pattern) (guard : pushGuard support p 29 30 31 46 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 46 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard17 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check17 (p : Pattern) : (!pushGuard support p 29 30 31 46 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 46 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound17 p)
theorem guard18 (p : Pattern) (guard : pushGuard support p 29 30 31 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound18 (p : Pattern) (guard : pushGuard support p 29 30 31 47 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 47 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard18 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check18 (p : Pattern) : (!pushGuard support p 29 30 31 47 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 47 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound18 p)
theorem guard19 (p : Pattern) (guard : pushGuard support p 29 30 31 48 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound19 (p : Pattern) (guard : pushGuard support p 29 30 31 48 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 48 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard19 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check19 (p : Pattern) : (!pushGuard support p 29 30 31 48 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 48 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound19 p)
theorem guard20 (p : Pattern) (guard : pushGuard support p 29 30 31 49 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound20 (p : Pattern) (guard : pushGuard support p 29 30 31 49 = true) : bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 49 + bonus 30 (change p 30 none) := by
  have certified := compare0 p (guard20 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 30 none)
  have normalized := agree75 _ _ (change_representative support p 30 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check20 (p : Pattern) : (!pushGuard support p 29 30 31 49 || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole 49 + bonus 30 (change p 30 none))) = true :=
  check_of_implication _ _ (bound20 p)
theorem guard21 (p : Pattern) (guard : walkGuard soko1_2.board support p 29 56 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound21 (p : Pattern) (guard : walkGuard soko1_2.board support p 29 56 .southEast = true) : bonus 29 p ≤ bonus 56 p := by
  have certified := compare0 p (guard21 p guard)
  simpa only [at29, at56, Int.zero_add] using certified
theorem check21 (p : Pattern) : (!walkGuard soko1_2.board support p 29 56 .southEast || decide (bonus 29 p ≤ bonus 56 p)) = true :=
  check_of_implication _ _ (bound21 p)
theorem guard22 (p : Pattern) (guard : walkGuard soko1_2.board support p 30 56 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound22 (p : Pattern) (guard : walkGuard soko1_2.board support p 30 56 .south = true) : bonus 30 p ≤ bonus 56 p := by
  have certified := compare0 p (guard22 p guard)
  simpa only [at30, at56, Int.zero_add] using certified
theorem check22 (p : Pattern) : (!walkGuard soko1_2.board support p 30 56 .south || decide (bonus 30 p ≤ bonus 56 p)) = true :=
  check_of_implication _ _ (bound22 p)
theorem guard23 (p : Pattern) (guard : pushGuard support p 30 56 82 82 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound23 (p : Pattern) (guard : pushGuard support p 30 56 82 82 = true) : bonus 30 p ≤ 1 + Generated.soko1_2Potential.boulder 82 - Generated.soko1_2Potential.boulder 56 + bonus 56 (change p 56 (some 82)) := by
  have certified := compare2 p (guard23 p guard)
  change d75 p ≤ (2 : Int) + d75 (change p 56 (some 82))
  have normalized := agree75 _ _ (change_representative support p 56 (some 82) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (2 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check23 (p : Pattern) : (!pushGuard support p 30 56 82 82 || decide (bonus 30 p ≤ 1 + Generated.soko1_2Potential.boulder 82 - Generated.soko1_2Potential.boulder 56 + bonus 56 (change p 56 (some 82)))) = true :=
  check_of_implication _ _ (bound23 p)
end NetHack.Sokoban12CostPartition
