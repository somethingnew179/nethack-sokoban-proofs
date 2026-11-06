import NetHack.Sokoban22Refined85.Goals
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard0 (p : Pattern) (guard : walkGuard soko2_2.board support p 25 47 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound0 (p : Pattern) (guard : walkGuard soko2_2.board support p 25 47 .south = true) : bonus 25 p ≤ bonus 47 p := by
  have certified := compare0 p (guard0 p guard)
  simpa only [at25, at47, Int.zero_add] using certified
theorem check0 (p : Pattern) : (!walkGuard soko2_2.board support p 25 47 .south || decide (bonus 25 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound0 p)
theorem guard1 (p : Pattern) (guard : pushGuard support p 25 47 69 69 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1 (p : Pattern) (guard : pushGuard support p 25 47 69 69 = true) : bonus 25 p ≤ 1 + Generated.soko2_2Potential.boulder 69 - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some 69)) := by
  have certified := compare1 p (guard1 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 47 (some 69))
  have normalized := agree267 _ _ (change_representative support p 47 (some 69) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check1 (p : Pattern) : (!pushGuard support p 25 47 69 69 || decide (bonus 25 p ≤ 1 + Generated.soko2_2Potential.boulder 69 - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some 69)))) = true :=
  check_of_implication _ _ (bound1 p)
theorem guard2 (p : Pattern) (guard : walkGuard soko2_2.board support p 25 48 .southEast = true) : d4038 p = 1 := by
  change (!false && !(p 48) && !(true && false && true)) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound2 (p : Pattern) (guard : walkGuard soko2_2.board support p 25 48 .southEast = true) : bonus 25 p ≤ bonus 48 p := by
  have certified := compare4 p (guard2 p guard)
  simpa only [at25, at48, Int.zero_add] using certified
theorem check2 (p : Pattern) : (!walkGuard soko2_2.board support p 25 48 .southEast || decide (bonus 25 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound2 p)
theorem guard3 (p : Pattern) (guard : walkGuard soko2_2.board support p 25 46 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound3 (p : Pattern) (guard : walkGuard soko2_2.board support p 25 46 .southWest = true) : bonus 25 p ≤ bonus 46 p := by
  have certified := compare0 p (guard3 p guard)
  simpa only [at25, at46, Int.zero_add] using certified
theorem check3 (p : Pattern) : (!walkGuard soko2_2.board support p 25 46 .southWest || decide (bonus 25 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound3 p)
theorem guard4 (p : Pattern) (guard : walkGuard soko2_2.board support p 27 49 .south = true) : d4040 p = 1 := by
  change (!false && !(p 49) && !false) = true at guard
  cases h49 : p 49
  all_goals simp [d0, d1, d4040, h49] at guard ⊢
theorem bound4 (p : Pattern) (guard : walkGuard soko2_2.board support p 27 49 .south = true) : bonus 27 p ≤ bonus 49 p := by
  have certified := compare10 p (guard4 p guard)
  simpa only [at27, at49, Int.zero_add] using certified
theorem check4 (p : Pattern) : (!walkGuard soko2_2.board support p 27 49 .south || decide (bonus 27 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound4 p)
theorem guard5 (p : Pattern) (guard : pushGuard support p 27 49 71 71 = true) : d4043 p = 1 := by
  change (!false && (!true || (p 49)) && !(p 71) && (!(p 71) || false)) = true at guard
  cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4042, d4043, h49, h71] at guard ⊢
theorem bound5 (p : Pattern) (guard : pushGuard support p 27 49 71 71 = true) : bonus 27 p ≤ 1 + Generated.soko2_2Potential.boulder 71 - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some 71)) := by
  have certified := compare18 p (guard5 p guard)
  change d312 p ≤ (0 : Int) + d484 (change p 49 (some 71))
  have normalized := agree484 _ _ (change_representative support p 49 (some 71) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (0 : Int) + d484 (change p 49 (some 71))
  rw [sub367]
  exact certified
theorem check5 (p : Pattern) : (!pushGuard support p 27 49 71 71 || decide (bonus 27 p ≤ 1 + Generated.soko2_2Potential.boulder 71 - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some 71)))) = true :=
  check_of_implication _ _ (bound5 p)
theorem guard6 (p : Pattern) (guard : walkGuard soko2_2.board support p 27 28 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound6 (p : Pattern) (guard : walkGuard soko2_2.board support p 27 28 .east = true) : bonus 27 p ≤ bonus 28 p := by
  have certified := compare19 p (guard6 p guard)
  simpa only [at27, at28, Int.zero_add] using certified
theorem check6 (p : Pattern) : (!walkGuard soko2_2.board support p 27 28 .east || decide (bonus 27 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound6 p)
theorem guard7 (p : Pattern) (guard : pushGuard support p 27 28 29 29 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound7 (p : Pattern) (guard : pushGuard support p 27 28 29 29 = true) : bonus 27 p ≤ 1 + Generated.soko2_2Potential.boulder 29 - Generated.soko2_2Potential.boulder 28 + bonus 28 (change p 28 (some 29)) := by
  have certified := compare20 p (guard7 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 28 (some 29))
  have normalized := agree312 _ _ (change_representative support p 28 (some 29) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check7 (p : Pattern) : (!pushGuard support p 27 28 29 29 || decide (bonus 27 p ≤ 1 + Generated.soko2_2Potential.boulder 29 - Generated.soko2_2Potential.boulder 28 + bonus 28 (change p 28 (some 29)))) = true :=
  check_of_implication _ _ (bound7 p)
theorem guard8 (p : Pattern) (guard : walkGuard soko2_2.board support p 27 50 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 49) && false)) = true at guard
  cases h49 : p 49
  all_goals simp [d1, h49] at guard ⊢
theorem bound8 (p : Pattern) (guard : walkGuard soko2_2.board support p 27 50 .southEast = true) : bonus 27 p ≤ bonus 50 p := by
  have certified := compare19 p (guard8 p guard)
  simpa only [at27, at50, Int.zero_add] using certified
theorem check8 (p : Pattern) : (!walkGuard soko2_2.board support p 27 50 .southEast || decide (bonus 27 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound8 p)
theorem guard9 (p : Pattern) (guard : walkGuard soko2_2.board support p 27 48 .southWest = true) : d4044 p = 1 := by
  change (!false && !(p 48) && !(true && (p 49) && true)) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49
  all_goals simp [d0, d1, d4040, d4044, h48, h49] at guard ⊢
theorem bound9 (p : Pattern) (guard : walkGuard soko2_2.board support p 27 48 .southWest = true) : bonus 27 p ≤ bonus 48 p := by
  have certified := compare23 p (guard9 p guard)
  simpa only [at27, at48, Int.zero_add] using certified
theorem check9 (p : Pattern) : (!walkGuard soko2_2.board support p 27 48 .southWest || decide (bonus 27 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound9 p)
theorem guard10 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 50 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound10 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 50 .south = true) : bonus 28 p ≤ bonus 50 p := by
  have certified := compare19 p (guard10 p guard)
  simpa only [at28, at50, Int.zero_add] using certified
theorem check10 (p : Pattern) : (!walkGuard soko2_2.board support p 28 50 .south || decide (bonus 28 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound10 p)
theorem guard11 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 29 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound11 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 29 .east = true) : bonus 28 p ≤ bonus 29 p := by
  have certified := compare19 p (guard11 p guard)
  simpa only [at28, at29, Int.zero_add] using certified
theorem check11 (p : Pattern) : (!walkGuard soko2_2.board support p 28 29 .east || decide (bonus 28 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound11 p)
theorem guard12 (p : Pattern) (guard : pushGuard support p 28 29 30 30 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound12 (p : Pattern) (guard : pushGuard support p 28 29 30 30 = true) : bonus 28 p ≤ 1 + Generated.soko2_2Potential.boulder 30 - Generated.soko2_2Potential.boulder 29 + bonus 29 (change p 29 (some 30)) := by
  have certified := compare20 p (guard12 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 29 (some 30))
  have normalized := agree312 _ _ (change_representative support p 29 (some 30) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check12 (p : Pattern) : (!pushGuard support p 28 29 30 30 || decide (bonus 28 p ≤ 1 + Generated.soko2_2Potential.boulder 30 - Generated.soko2_2Potential.boulder 29 + bonus 29 (change p 29 (some 30)))) = true :=
  check_of_implication _ _ (bound12 p)
theorem guard13 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 27 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound13 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 27 .west = true) : bonus 28 p ≤ bonus 27 p := by
  have certified := compare19 p (guard13 p guard)
  simpa only [at28, at27, Int.zero_add] using certified
theorem check13 (p : Pattern) : (!walkGuard soko2_2.board support p 28 27 .west || decide (bonus 28 p ≤ bonus 27 p)) = true :=
  check_of_implication _ _ (bound13 p)
theorem guard14 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 51 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound14 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 51 .southEast = true) : bonus 28 p ≤ bonus 51 p := by
  have certified := compare19 p (guard14 p guard)
  simpa only [at28, at51, Int.zero_add] using certified
theorem check14 (p : Pattern) : (!walkGuard soko2_2.board support p 28 51 .southEast || decide (bonus 28 p ≤ bonus 51 p)) = true :=
  check_of_implication _ _ (bound14 p)
theorem guard15 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 49 .southWest = true) : d4040 p = 1 := by
  change (!false && !(p 49) && !(true && false && false)) = true at guard
  cases h49 : p 49
  all_goals simp [d0, d1, d4040, h49] at guard ⊢
theorem bound15 (p : Pattern) (guard : walkGuard soko2_2.board support p 28 49 .southWest = true) : bonus 28 p ≤ bonus 49 p := by
  have certified := compare10 p (guard15 p guard)
  simpa only [at28, at49, Int.zero_add] using certified
theorem check15 (p : Pattern) : (!walkGuard soko2_2.board support p 28 49 .southWest || decide (bonus 28 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound15 p)
theorem guard16 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 51 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound16 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 51 .south = true) : bonus 29 p ≤ bonus 51 p := by
  have certified := compare19 p (guard16 p guard)
  simpa only [at29, at51, Int.zero_add] using certified
theorem check16 (p : Pattern) : (!walkGuard soko2_2.board support p 29 51 .south || decide (bonus 29 p ≤ bonus 51 p)) = true :=
  check_of_implication _ _ (bound16 p)
theorem guard17 (p : Pattern) (guard : pushGuard support p 29 51 73 73 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound17 (p : Pattern) (guard : pushGuard support p 29 51 73 73 = true) : bonus 29 p ≤ 1 + Generated.soko2_2Potential.boulder 73 - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some 73)) := by
  have certified := compare20 p (guard17 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 51 (some 73))
  have normalized := agree312 _ _ (change_representative support p 51 (some 73) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check17 (p : Pattern) : (!pushGuard support p 29 51 73 73 || decide (bonus 29 p ≤ 1 + Generated.soko2_2Potential.boulder 73 - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some 73)))) = true :=
  check_of_implication _ _ (bound17 p)
theorem guard18 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 30 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound18 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 30 .east = true) : bonus 29 p ≤ bonus 30 p := by
  have certified := compare19 p (guard18 p guard)
  simpa only [at29, at30, Int.zero_add] using certified
theorem check18 (p : Pattern) : (!walkGuard soko2_2.board support p 29 30 .east || decide (bonus 29 p ≤ bonus 30 p)) = true :=
  check_of_implication _ _ (bound18 p)
theorem guard19 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 28 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound19 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 28 .west = true) : bonus 29 p ≤ bonus 28 p := by
  have certified := compare19 p (guard19 p guard)
  simpa only [at29, at28, Int.zero_add] using certified
theorem check19 (p : Pattern) : (!walkGuard soko2_2.board support p 29 28 .west || decide (bonus 29 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound19 p)
theorem guard20 (p : Pattern) (guard : pushGuard support p 29 28 27 27 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound20 (p : Pattern) (guard : pushGuard support p 29 28 27 27 = true) : bonus 29 p ≤ 1 + Generated.soko2_2Potential.boulder 27 - Generated.soko2_2Potential.boulder 28 + bonus 28 (change p 28 (some 27)) := by
  have certified := compare20 p (guard20 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 28 (some 27))
  have normalized := agree312 _ _ (change_representative support p 28 (some 27) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check20 (p : Pattern) : (!pushGuard support p 29 28 27 27 || decide (bonus 29 p ≤ 1 + Generated.soko2_2Potential.boulder 27 - Generated.soko2_2Potential.boulder 28 + bonus 28 (change p 28 (some 27)))) = true :=
  check_of_implication _ _ (bound20 p)
theorem guard21 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 52 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound21 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 52 .southEast = true) : bonus 29 p ≤ bonus 52 p := by
  have certified := compare19 p (guard21 p guard)
  simpa only [at29, at52, Int.zero_add] using certified
theorem check21 (p : Pattern) : (!walkGuard soko2_2.board support p 29 52 .southEast || decide (bonus 29 p ≤ bonus 52 p)) = true :=
  check_of_implication _ _ (bound21 p)
theorem guard22 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 50 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound22 (p : Pattern) (guard : walkGuard soko2_2.board support p 29 50 .southWest = true) : bonus 29 p ≤ bonus 50 p := by
  have certified := compare19 p (guard22 p guard)
  simpa only [at29, at50, Int.zero_add] using certified
theorem check22 (p : Pattern) : (!walkGuard soko2_2.board support p 29 50 .southWest || decide (bonus 29 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound22 p)
theorem guard23 (p : Pattern) (guard : walkGuard soko2_2.board support p 30 52 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound23 (p : Pattern) (guard : walkGuard soko2_2.board support p 30 52 .south = true) : bonus 30 p ≤ bonus 52 p := by
  have certified := compare19 p (guard23 p guard)
  simpa only [at30, at52, Int.zero_add] using certified
theorem check23 (p : Pattern) : (!walkGuard soko2_2.board support p 30 52 .south || decide (bonus 30 p ≤ bonus 52 p)) = true :=
  check_of_implication _ _ (bound23 p)
end NetHack.Sokoban22Refined85
