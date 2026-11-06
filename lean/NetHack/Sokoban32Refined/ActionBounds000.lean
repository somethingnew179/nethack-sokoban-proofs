import NetHack.Sokoban32Refined.Goals
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard0 (p : Pattern) (guard : walkGuard soko3_2.board support p 28 54 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound0 (p : Pattern) (guard : walkGuard soko3_2.board support p 28 54 .south = true) : bonus 28 p ≤ bonus 54 p := by
  have certified := compare0 p (guard0 p guard)
  simpa only [at28, at54, Int.zero_add] using certified
theorem check0 (p : Pattern) : (!walkGuard soko3_2.board support p 28 54 .south || decide (bonus 28 p ≤ bonus 54 p)) = true :=
  check_of_implication _ _ (bound0 p)
theorem guard1 (p : Pattern) (guard : pushGuard support p 28 54 80 80 = true) : d827 p = 1 := by
  change (!false && (!false || false) && !(p 80) && (!(p 80) || false)) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound1 (p : Pattern) (guard : pushGuard support p 28 54 80 80 = true) : bonus 28 p ≤ 1 + Generated.soko3_2Potential.boulder 80 - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some 80)) := by
  have certified := compare102 p (guard1 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 54 (some 80))
  have normalized := agree134 _ _ (change_representative support p 54 (some 80) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 (some 80))
  rw [sub114]
  exact certified
theorem check1 (p : Pattern) : (!pushGuard support p 28 54 80 80 || decide (bonus 28 p ≤ 1 + Generated.soko3_2Potential.boulder 80 - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some 80)))) = true :=
  check_of_implication _ _ (bound1 p)
theorem guard2 (p : Pattern) (guard : walkGuard soko3_2.board support p 28 29 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound2 (p : Pattern) (guard : walkGuard soko3_2.board support p 28 29 .east = true) : bonus 28 p ≤ bonus 29 p := by
  have certified := compare0 p (guard2 p guard)
  simpa only [at28, at29, Int.zero_add] using certified
theorem check2 (p : Pattern) : (!walkGuard soko3_2.board support p 28 29 .east || decide (bonus 28 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound2 p)
theorem guard3 (p : Pattern) (guard : walkGuard soko3_2.board support p 28 55 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound3 (p : Pattern) (guard : walkGuard soko3_2.board support p 28 55 .southEast = true) : bonus 28 p ≤ bonus 55 p := by
  have certified := compare0 p (guard3 p guard)
  simpa only [at28, at55, Int.zero_add] using certified
theorem check3 (p : Pattern) : (!walkGuard soko3_2.board support p 28 55 .southEast || decide (bonus 28 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound3 p)
theorem guard4 (p : Pattern) (guard : walkGuard soko3_2.board support p 28 53 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound4 (p : Pattern) (guard : walkGuard soko3_2.board support p 28 53 .southWest = true) : bonus 28 p ≤ bonus 53 p := by
  have certified := compare0 p (guard4 p guard)
  simpa only [at28, at53, Int.zero_add] using certified
theorem check4 (p : Pattern) : (!walkGuard soko3_2.board support p 28 53 .southWest || decide (bonus 28 p ≤ bonus 53 p)) = true :=
  check_of_implication _ _ (bound4 p)
theorem guard5 (p : Pattern) (guard : walkGuard soko3_2.board support p 29 55 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound5 (p : Pattern) (guard : walkGuard soko3_2.board support p 29 55 .south = true) : bonus 29 p ≤ bonus 55 p := by
  have certified := compare0 p (guard5 p guard)
  simpa only [at29, at55, Int.zero_add] using certified
theorem check5 (p : Pattern) : (!walkGuard soko3_2.board support p 29 55 .south || decide (bonus 29 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound5 p)
theorem guard6 (p : Pattern) (guard : walkGuard soko3_2.board support p 29 28 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound6 (p : Pattern) (guard : walkGuard soko3_2.board support p 29 28 .west = true) : bonus 29 p ≤ bonus 28 p := by
  have certified := compare0 p (guard6 p guard)
  simpa only [at29, at28, Int.zero_add] using certified
theorem check6 (p : Pattern) : (!walkGuard soko3_2.board support p 29 28 .west || decide (bonus 29 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound6 p)
theorem guard7 (p : Pattern) (guard : walkGuard soko3_2.board support p 29 56 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound7 (p : Pattern) (guard : walkGuard soko3_2.board support p 29 56 .southEast = true) : bonus 29 p ≤ bonus 56 p := by
  have certified := compare0 p (guard7 p guard)
  simpa only [at29, at56, Int.zero_add] using certified
theorem check7 (p : Pattern) : (!walkGuard soko3_2.board support p 29 56 .southEast || decide (bonus 29 p ≤ bonus 56 p)) = true :=
  check_of_implication _ _ (bound7 p)
theorem guard8 (p : Pattern) (guard : walkGuard soko3_2.board support p 29 54 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound8 (p : Pattern) (guard : walkGuard soko3_2.board support p 29 54 .southWest = true) : bonus 29 p ≤ bonus 54 p := by
  have certified := compare0 p (guard8 p guard)
  simpa only [at29, at54, Int.zero_add] using certified
theorem check8 (p : Pattern) : (!walkGuard soko3_2.board support p 29 54 .southWest || decide (bonus 29 p ≤ bonus 54 p)) = true :=
  check_of_implication _ _ (bound8 p)
theorem guard9 (p : Pattern) (guard : walkGuard soko3_2.board support p 42 68 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound9 (p : Pattern) (guard : walkGuard soko3_2.board support p 42 68 .south = true) : bonus 42 p ≤ bonus 68 p := by
  have certified := compare103 p (guard9 p guard)
  simpa only [at42, at68, Int.zero_add] using certified
theorem check9 (p : Pattern) : (!walkGuard soko3_2.board support p 42 68 .south || decide (bonus 42 p ≤ bonus 68 p)) = true :=
  check_of_implication _ _ (bound9 p)
theorem guard10 (p : Pattern) (guard : pushGuard support p 42 68 94 94 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound10 (p : Pattern) (guard : pushGuard support p 42 68 94 94 = true) : bonus 42 p ≤ 1 + Generated.soko3_2Potential.boulder 94 - Generated.soko3_2Potential.boulder 68 + bonus 68 (change p 68 (some 94)) := by
  have certified := compare37 p (guard10 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 68 (some 94))
  have normalized := agree0 _ _ (change_representative support p 68 (some 94) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check10 (p : Pattern) : (!pushGuard support p 42 68 94 94 || decide (bonus 42 p ≤ 1 + Generated.soko3_2Potential.boulder 94 - Generated.soko3_2Potential.boulder 68 + bonus 68 (change p 68 (some 94)))) = true :=
  check_of_implication _ _ (bound10 p)
theorem guard11 (p : Pattern) (guard : walkGuard soko3_2.board support p 42 43 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound11 (p : Pattern) (guard : walkGuard soko3_2.board support p 42 43 .east = true) : bonus 42 p ≤ bonus 43 p := by
  have certified := compare103 p (guard11 p guard)
  simpa only [at42, at43, Int.zero_add] using certified
theorem check11 (p : Pattern) : (!walkGuard soko3_2.board support p 42 43 .east || decide (bonus 42 p ≤ bonus 43 p)) = true :=
  check_of_implication _ _ (bound11 p)
theorem guard12 (p : Pattern) (guard : pushGuard support p 42 43 44 44 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound12 (p : Pattern) (guard : pushGuard support p 42 43 44 44 = true) : bonus 42 p ≤ 1 + Generated.soko3_2Potential.boulder 44 - Generated.soko3_2Potential.boulder 43 + bonus 43 (change p 43 (some 44)) := by
  have certified := compare37 p (guard12 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 43 (some 44))
  have normalized := agree0 _ _ (change_representative support p 43 (some 44) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check12 (p : Pattern) : (!pushGuard support p 42 43 44 44 || decide (bonus 42 p ≤ 1 + Generated.soko3_2Potential.boulder 44 - Generated.soko3_2Potential.boulder 43 + bonus 43 (change p 43 (some 44)))) = true :=
  check_of_implication _ _ (bound12 p)
theorem guard13 (p : Pattern) (guard : walkGuard soko3_2.board support p 42 69 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound13 (p : Pattern) (guard : walkGuard soko3_2.board support p 42 69 .southEast = true) : bonus 42 p ≤ bonus 69 p := by
  have certified := compare103 p (guard13 p guard)
  simpa only [at42, at69, Int.zero_add] using certified
theorem check13 (p : Pattern) : (!walkGuard soko3_2.board support p 42 69 .southEast || decide (bonus 42 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound13 p)
theorem guard14 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 69 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound14 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 69 .south = true) : bonus 43 p ≤ bonus 69 p := by
  have certified := compare103 p (guard14 p guard)
  simpa only [at43, at69, Int.zero_add] using certified
theorem check14 (p : Pattern) : (!walkGuard soko3_2.board support p 43 69 .south || decide (bonus 43 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound14 p)
theorem guard15 (p : Pattern) (guard : pushGuard support p 43 69 95 95 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound15 (p : Pattern) (guard : pushGuard support p 43 69 95 95 = true) : bonus 43 p ≤ 1 + Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some 95)) := by
  have certified := compare37 p (guard15 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 69 (some 95))
  have normalized := agree0 _ _ (change_representative support p 69 (some 95) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check15 (p : Pattern) : (!pushGuard support p 43 69 95 95 || decide (bonus 43 p ≤ 1 + Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some 95)))) = true :=
  check_of_implication _ _ (bound15 p)
theorem guard16 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 44 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound16 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 44 .east = true) : bonus 43 p ≤ bonus 44 p := by
  have certified := compare103 p (guard16 p guard)
  simpa only [at43, at44, Int.zero_add] using certified
theorem check16 (p : Pattern) : (!walkGuard soko3_2.board support p 43 44 .east || decide (bonus 43 p ≤ bonus 44 p)) = true :=
  check_of_implication _ _ (bound16 p)
theorem guard17 (p : Pattern) (guard : pushGuard support p 43 44 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound17 (p : Pattern) (guard : pushGuard support p 43 44 45 45 = true) : bonus 43 p ≤ 1 + Generated.soko3_2Potential.boulder 45 - Generated.soko3_2Potential.boulder 44 + bonus 44 (change p 44 (some 45)) := by
  have certified := compare37 p (guard17 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 44 (some 45))
  have normalized := agree0 _ _ (change_representative support p 44 (some 45) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check17 (p : Pattern) : (!pushGuard support p 43 44 45 45 || decide (bonus 43 p ≤ 1 + Generated.soko3_2Potential.boulder 45 - Generated.soko3_2Potential.boulder 44 + bonus 44 (change p 44 (some 45)))) = true :=
  check_of_implication _ _ (bound17 p)
theorem guard18 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 42 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound18 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 42 .west = true) : bonus 43 p ≤ bonus 42 p := by
  have certified := compare103 p (guard18 p guard)
  simpa only [at43, at42, Int.zero_add] using certified
theorem check18 (p : Pattern) : (!walkGuard soko3_2.board support p 43 42 .west || decide (bonus 43 p ≤ bonus 42 p)) = true :=
  check_of_implication _ _ (bound18 p)
theorem guard19 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 70 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound19 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 70 .southEast = true) : bonus 43 p ≤ bonus 70 p := by
  have certified := compare103 p (guard19 p guard)
  simpa only [at43, at70, Int.zero_add] using certified
theorem check19 (p : Pattern) : (!walkGuard soko3_2.board support p 43 70 .southEast || decide (bonus 43 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound19 p)
theorem guard20 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 68 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound20 (p : Pattern) (guard : walkGuard soko3_2.board support p 43 68 .southWest = true) : bonus 43 p ≤ bonus 68 p := by
  have certified := compare103 p (guard20 p guard)
  simpa only [at43, at68, Int.zero_add] using certified
theorem check20 (p : Pattern) : (!walkGuard soko3_2.board support p 43 68 .southWest || decide (bonus 43 p ≤ bonus 68 p)) = true :=
  check_of_implication _ _ (bound20 p)
theorem guard21 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 70 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound21 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 70 .south = true) : bonus 44 p ≤ bonus 70 p := by
  have certified := compare103 p (guard21 p guard)
  simpa only [at44, at70, Int.zero_add] using certified
theorem check21 (p : Pattern) : (!walkGuard soko3_2.board support p 44 70 .south || decide (bonus 44 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound21 p)
theorem guard22 (p : Pattern) (guard : pushGuard support p 44 70 96 96 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound22 (p : Pattern) (guard : pushGuard support p 44 70 96 96 = true) : bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some 96)) := by
  have certified := compare37 p (guard22 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 70 (some 96))
  have normalized := agree0 _ _ (change_representative support p 70 (some 96) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check22 (p : Pattern) : (!pushGuard support p 44 70 96 96 || decide (bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some 96)))) = true :=
  check_of_implication _ _ (bound22 p)
theorem guard23 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 45 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound23 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 45 .east = true) : bonus 44 p ≤ bonus 45 p := by
  have certified := compare103 p (guard23 p guard)
  simpa only [at44, at45, Int.zero_add] using certified
theorem check23 (p : Pattern) : (!walkGuard soko3_2.board support p 44 45 .east || decide (bonus 44 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound23 p)
end NetHack.Sokoban32Refined
