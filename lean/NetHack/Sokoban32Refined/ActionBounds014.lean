import NetHack.Sokoban32Refined.ActionBounds013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard336 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 75 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound336 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 75 .northWest = true) : bonus 102 p ≤ bonus 75 p := by
  have certified := compare103 p (guard336 p guard)
  simpa only [at102, at75, Int.zero_add] using certified
theorem check336 (p : Pattern) : (!walkGuard soko3_2.board support p 102 75 .northWest || decide (bonus 102 p ≤ bonus 75 p)) = true :=
  check_of_implication _ _ (bound336 p)
theorem guard337 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 127 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound337 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 127 .southWest = true) : bonus 102 p ≤ bonus 127 p := by
  have certified := compare103 p (guard337 p guard)
  simpa only [at102, at127, Int.zero_add] using certified
theorem check337 (p : Pattern) : (!walkGuard soko3_2.board support p 102 127 .southWest || decide (bonus 102 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound337 p)
theorem guard338 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 79 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound338 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 79 .north = true) : bonus 105 p ≤ bonus 79 p := by
  have certified := compare0 p (guard338 p guard)
  simpa only [at105, at79, Int.zero_add] using certified
theorem check338 (p : Pattern) : (!walkGuard soko3_2.board support p 105 79 .north || decide (bonus 105 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound338 p)
theorem guard339 (p : Pattern) (guard : pushGuard support p 105 79 53 53 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound339 (p : Pattern) (guard : pushGuard support p 105 79 53 53 = true) : bonus 105 p ≤ 1 + Generated.soko3_2Potential.boulder 53 - Generated.soko3_2Potential.boulder 79 + bonus 79 (change p 79 (some 53)) := by
  have certified := compare104 p (guard339 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 79 (some 53))
  have normalized := agree134 _ _ (change_representative support p 79 (some 53) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check339 (p : Pattern) : (!pushGuard support p 105 79 53 53 || decide (bonus 105 p ≤ 1 + Generated.soko3_2Potential.boulder 53 - Generated.soko3_2Potential.boulder 79 + bonus 79 (change p 79 (some 53)))) = true :=
  check_of_implication _ _ (bound339 p)
theorem guard340 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 131 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound340 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 131 .south = true) : bonus 105 p ≤ bonus 131 p := by
  have certified := compare0 p (guard340 p guard)
  simpa only [at105, at131, Int.zero_add] using certified
theorem check340 (p : Pattern) : (!walkGuard soko3_2.board support p 105 131 .south || decide (bonus 105 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound340 p)
theorem guard341 (p : Pattern) (guard : pushGuard support p 105 131 157 157 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound341 (p : Pattern) (guard : pushGuard support p 105 131 157 157 = true) : bonus 105 p ≤ 1 + Generated.soko3_2Potential.boulder 157 - Generated.soko3_2Potential.boulder 131 + bonus 131 (change p 131 (some 157)) := by
  have certified := compare104 p (guard341 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 131 (some 157))
  have normalized := agree134 _ _ (change_representative support p 131 (some 157) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check341 (p : Pattern) : (!pushGuard support p 105 131 157 157 || decide (bonus 105 p ≤ 1 + Generated.soko3_2Potential.boulder 157 - Generated.soko3_2Potential.boulder 131 + bonus 131 (change p 131 (some 157)))) = true :=
  check_of_implication _ _ (bound341 p)
theorem guard342 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 106 .east = true) : d829 p = 1 := by
  change (!false && !(p 106) && !false) = true at guard
  cases h106 : p 106
  all_goals simp [d0, d1, d829, h106] at guard ⊢
theorem bound342 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 106 .east = true) : bonus 105 p ≤ bonus 106 p := by
  have certified := compare297 p (guard342 p guard)
  simpa only [at105, at106, Int.zero_add] using certified
theorem check342 (p : Pattern) : (!walkGuard soko3_2.board support p 105 106 .east || decide (bonus 105 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound342 p)
theorem guard343 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 80 .northEast = true) : d827 p = 1 := by
  change (!false && !(p 80) && !(true && false && (p 106))) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106
  all_goals simp [d0, d1, d827, h80, h106] at guard ⊢
theorem bound343 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 80 .northEast = true) : bonus 105 p ≤ bonus 80 p := by
  have certified := compare107 p (guard343 p guard)
  simpa only [at105, at80, Int.zero_add] using certified
theorem check343 (p : Pattern) : (!walkGuard soko3_2.board support p 105 80 .northEast || decide (bonus 105 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound343 p)
theorem guard344 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 132 .southEast = true) : d841 p = 1 := by
  change (!false && !(p 132) && !(true && false && (p 106))) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132
  all_goals simp [d0, d1, d841, h106, h132] at guard ⊢
theorem bound344 (p : Pattern) (guard : walkGuard soko3_2.board support p 105 132 .southEast = true) : bonus 105 p ≤ bonus 132 p := by
  have certified := compare612 p (guard344 p guard)
  simpa only [at105, at132, Int.zero_add] using certified
theorem check344 (p : Pattern) : (!walkGuard soko3_2.board support p 105 132 .southEast || decide (bonus 105 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound344 p)
theorem guard345 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 80 .north = true) : d838 p = 1 := by
  change (!(p 106) && !(p 80) && !false) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106
  all_goals simp [d0, d1, d829, d838, h80, h106] at guard ⊢
theorem bound345 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 80 .north = true) : bonus 106 p ≤ bonus 80 p := by
  have certified := compare619 p (guard345 p guard)
  simpa only [at106, at80, Int.zero_add] using certified
theorem check345 (p : Pattern) : (!walkGuard soko3_2.board support p 106 80 .north || decide (bonus 106 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound345 p)
theorem guard346 (p : Pattern) (guard : pushGuard support p 106 80 54 54 = true) : d830 p = 1 := by
  change (!(p 106) && (!true || (p 80)) && !false && (!false || false)) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106
  all_goals simp [d0, d1, d829, d830, h80, h106] at guard ⊢
theorem bound346 (p : Pattern) (guard : pushGuard support p 106 80 54 54 = true) : bonus 106 p ≤ 1 + Generated.soko3_2Potential.boulder 54 - Generated.soko3_2Potential.boulder 80 + bonus 80 (change p 80 (some 54)) := by
  have certified := compare646 p (guard346 p guard)
  change d183 p ≤ (1 : Int) + d173 (change p 80 (some 54))
  have normalized := agree173 _ _ (change_representative support p 80 (some 54) 10000 dummy_outside)
  rw [normalized]
  change d183 p ≤ (1 : Int) + d173 (change p 80 none)
  rw [sub722]
  exact certified
theorem check346 (p : Pattern) : (!pushGuard support p 106 80 54 54 || decide (bonus 106 p ≤ 1 + Generated.soko3_2Potential.boulder 54 - Generated.soko3_2Potential.boulder 80 + bonus 80 (change p 80 (some 54)))) = true :=
  check_of_implication _ _ (bound346 p)
theorem guard347 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 132 .south = true) : d870 p = 1 := by
  change (!(p 106) && !(p 132) && !false) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132
  all_goals simp [d0, d1, d841, d870, h106, h132] at guard ⊢
theorem bound347 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 132 .south = true) : bonus 106 p ≤ bonus 132 p := by
  have certified := compare657 p (guard347 p guard)
  simpa only [at106, at132, Int.zero_add] using certified
theorem check347 (p : Pattern) : (!walkGuard soko3_2.board support p 106 132 .south || decide (bonus 106 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound347 p)
theorem guard348 (p : Pattern) (guard : pushGuard support p 106 132 158 158 = true) : d875 p = 1 := by
  change (!(p 106) && (!true || (p 132)) && !(p 158) && (!(p 158) || false)) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d873, d874, d875, h106, h132, h158] at guard ⊢
theorem bound348 (p : Pattern) (guard : pushGuard support p 106 132 158 158 = true) : bonus 106 p ≤ 1 + Generated.soko3_2Potential.boulder 158 - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some 158)) := by
  have certified := compare780 p (guard348 p guard)
  change d183 p ≤ (0 : Int) + d292 (change p 132 (some 158))
  have normalized := agree292 _ _ (change_representative support p 132 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d183 p ≤ (0 : Int) + d292 (change p 132 (some 158))
  rw [sub802]
  exact certified
theorem check348 (p : Pattern) : (!pushGuard support p 106 132 158 158 || decide (bonus 106 p ≤ 1 + Generated.soko3_2Potential.boulder 158 - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some 158)))) = true :=
  check_of_implication _ _ (bound348 p)
theorem guard349 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 105 .west = true) : d829 p = 1 := by
  change (!(p 106) && !false && !false) = true at guard
  cases h106 : p 106
  all_goals simp [d0, d1, d829, h106] at guard ⊢
theorem bound349 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 105 .west = true) : bonus 106 p ≤ bonus 105 p := by
  have certified := compare786 p (guard349 p guard)
  simpa only [at106, at105, Int.zero_add] using certified
theorem check349 (p : Pattern) : (!walkGuard soko3_2.board support p 106 105 .west || decide (bonus 106 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound349 p)
theorem guard350 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 79 .northWest = true) : d829 p = 1 := by
  change (!(p 106) && !false && !(true && (p 80) && false)) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106
  all_goals simp [d0, d1, d829, h80, h106] at guard ⊢
theorem bound350 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 79 .northWest = true) : bonus 106 p ≤ bonus 79 p := by
  have certified := compare786 p (guard350 p guard)
  simpa only [at106, at79, Int.zero_add] using certified
theorem check350 (p : Pattern) : (!walkGuard soko3_2.board support p 106 79 .northWest || decide (bonus 106 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound350 p)
theorem guard351 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 133 .southEast = true) : d913 p = 1 := by
  change (!(p 106) && !(p 133) && !(true && (p 132) && true)) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d910, d912, d913, h106, h132, h133] at guard ⊢
theorem bound351 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 133 .southEast = true) : bonus 106 p ≤ bonus 133 p := by
  have certified := compare841 p (guard351 p guard)
  simpa only [at106, at133, Int.zero_add] using certified
theorem check351 (p : Pattern) : (!walkGuard soko3_2.board support p 106 133 .southEast || decide (bonus 106 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound351 p)
theorem guard352 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 131 .southWest = true) : d829 p = 1 := by
  change (!(p 106) && !false && !(true && (p 132) && false)) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132
  all_goals simp [d0, d1, d829, h106, h132] at guard ⊢
theorem bound352 (p : Pattern) (guard : walkGuard soko3_2.board support p 106 131 .southWest = true) : bonus 106 p ≤ bonus 131 p := by
  have certified := compare786 p (guard352 p guard)
  simpa only [at106, at131, Int.zero_add] using certified
theorem check352 (p : Pattern) : (!walkGuard soko3_2.board support p 106 131 .southWest || decide (bonus 106 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound352 p)
theorem guard353 (p : Pattern) (guard : walkGuard soko3_2.board support p 108 134 .south = true) : d915 p = 1 := by
  change (!false && !(p 134) && !false) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d915, h134] at guard ⊢
theorem bound353 (p : Pattern) (guard : walkGuard soko3_2.board support p 108 134 .south = true) : bonus 108 p ≤ bonus 134 p := by
  have certified := compare945 p (guard353 p guard)
  simpa only [at108, at134, Int.zero_add] using certified
theorem check353 (p : Pattern) : (!walkGuard soko3_2.board support p 108 134 .south || decide (bonus 108 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound353 p)
theorem guard354 (p : Pattern) (guard : pushGuard support p 108 134 160 160 = true) : d918 p = 1 := by
  change (!false && (!true || (p 134)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d918, h134, h160] at guard ⊢
theorem bound354 (p : Pattern) (guard : pushGuard support p 108 134 160 160 = true) : bonus 108 p ≤ 1 + Generated.soko3_2Potential.boulder 160 - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some 160)) := by
  have certified := compare1105 p (guard354 p guard)
  change d134 p ≤ (0 : Int) + d388 (change p 134 (some 160))
  have normalized := agree388 _ _ (change_representative support p 134 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d388 (change p 134 (some 160))
  rw [sub896]
  exact certified
theorem check354 (p : Pattern) : (!pushGuard support p 108 134 160 160 || decide (bonus 108 p ≤ 1 + Generated.soko3_2Potential.boulder 160 - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some 160)))) = true :=
  check_of_implication _ _ (bound354 p)
theorem guard355 (p : Pattern) (guard : walkGuard soko3_2.board support p 108 109 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound355 (p : Pattern) (guard : walkGuard soko3_2.board support p 108 109 .east = true) : bonus 108 p ≤ bonus 109 p := by
  have certified := compare0 p (guard355 p guard)
  simpa only [at108, at109, Int.zero_add] using certified
theorem check355 (p : Pattern) : (!walkGuard soko3_2.board support p 108 109 .east || decide (bonus 108 p ≤ bonus 109 p)) = true :=
  check_of_implication _ _ (bound355 p)
theorem guard356 (p : Pattern) (guard : pushGuard support p 108 109 110 110 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound356 (p : Pattern) (guard : pushGuard support p 108 109 110 110 = true) : bonus 108 p ≤ 1 + Generated.soko3_2Potential.boulder 110 - Generated.soko3_2Potential.boulder 109 + bonus 109 (change p 109 (some 110)) := by
  have certified := compare104 p (guard356 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 109 (some 110))
  have normalized := agree134 _ _ (change_representative support p 109 (some 110) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check356 (p : Pattern) : (!pushGuard support p 108 109 110 110 || decide (bonus 108 p ≤ 1 + Generated.soko3_2Potential.boulder 110 - Generated.soko3_2Potential.boulder 109 + bonus 109 (change p 109 (some 110)))) = true :=
  check_of_implication _ _ (bound356 p)
theorem guard357 (p : Pattern) (guard : walkGuard soko3_2.board support p 108 135 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 134) && false)) = true at guard
  cases h134 : p 134
  all_goals simp [d1, h134] at guard ⊢
theorem bound357 (p : Pattern) (guard : walkGuard soko3_2.board support p 108 135 .southEast = true) : bonus 108 p ≤ bonus 135 p := by
  have certified := compare0 p (guard357 p guard)
  simpa only [at108, at135, Int.zero_add] using certified
theorem check357 (p : Pattern) : (!walkGuard soko3_2.board support p 108 135 .southEast || decide (bonus 108 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound357 p)
theorem guard358 (p : Pattern) (guard : walkGuard soko3_2.board support p 108 133 .southWest = true) : d984 p = 1 := by
  change (!false && !(p 133) && !(true && (p 134) && true)) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d915, d984, h133, h134] at guard ⊢
theorem bound358 (p : Pattern) (guard : walkGuard soko3_2.board support p 108 133 .southWest = true) : bonus 108 p ≤ bonus 133 p := by
  have certified := compare1212 p (guard358 p guard)
  simpa only [at108, at133, Int.zero_add] using certified
theorem check358 (p : Pattern) : (!walkGuard soko3_2.board support p 108 133 .southWest || decide (bonus 108 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound358 p)
theorem guard359 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 135 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound359 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 135 .south = true) : bonus 109 p ≤ bonus 135 p := by
  have certified := compare0 p (guard359 p guard)
  simpa only [at109, at135, Int.zero_add] using certified
theorem check359 (p : Pattern) : (!walkGuard soko3_2.board support p 109 135 .south || decide (bonus 109 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound359 p)
end NetHack.Sokoban32Refined
