import NetHack.Sokoban22Refined85.ActionBounds001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard48 (p : Pattern) (guard : pushGuard support p 48 49 50 50 = true) : d4046 p = 1 := by
  change (!(p 48) && (!true || (p 49)) && !false && (!false || false)) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49
  all_goals simp [d0, d1, d4039, d4046, h48, h49] at guard ⊢
theorem bound48 (p : Pattern) (guard : pushGuard support p 48 49 50 50 = true) : bonus 48 p ≤ 1 + Generated.soko2_2Potential.boulder 50 - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some 50)) := by
  have certified := compare529 p (guard48 p guard)
  change d481 p ≤ (1 : Int) + d484 (change p 49 (some 50))
  have normalized := agree484 _ _ (change_representative support p 49 (some 50) 10000 dummy_outside)
  rw [normalized]
  change d481 p ≤ (1 : Int) + d484 (change p 49 none)
  rw [sub930]
  exact certified
theorem check48 (p : Pattern) : (!pushGuard support p 48 49 50 50 || decide (bonus 48 p ≤ 1 + Generated.soko2_2Potential.boulder 50 - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some 50)))) = true :=
  check_of_implication _ _ (bound48 p)
theorem guard49 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 47 .west = true) : d4038 p = 1 := by
  change (!(p 48) && !false && !false) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound49 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 47 .west = true) : bonus 48 p ≤ bonus 47 p := by
  have certified := compare438 p (guard49 p guard)
  simpa only [at48, at47, Int.zero_add] using certified
theorem check49 (p : Pattern) : (!walkGuard soko2_2.board support p 48 47 .west || decide (bonus 48 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound49 p)
theorem guard50 (p : Pattern) (guard : pushGuard support p 48 47 46 46 = true) : d4038 p = 1 := by
  change (!(p 48) && (!false || false) && !false && (!false || false)) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound50 (p : Pattern) (guard : pushGuard support p 48 47 46 46 = true) : bonus 48 p ≤ 1 + Generated.soko2_2Potential.boulder 46 - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some 46)) := by
  have certified := compare532 p (guard50 p guard)
  change d481 p ≤ (1 : Int) + d267 (change p 47 (some 46))
  have normalized := agree267 _ _ (change_representative support p 47 (some 46) 10000 dummy_outside)
  rw [normalized]
  change d481 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check50 (p : Pattern) : (!pushGuard support p 48 47 46 46 || decide (bonus 48 p ≤ 1 + Generated.soko2_2Potential.boulder 46 - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some 46)))) = true :=
  check_of_implication _ _ (bound50 p)
theorem guard51 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 27 .northEast = true) : d4044 p = 1 := by
  change (!(p 48) && !false && !(true && true && (p 49))) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49
  all_goals simp [d0, d1, d4040, d4044, h48, h49] at guard ⊢
theorem bound51 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 27 .northEast = true) : bonus 48 p ≤ bonus 27 p := by
  have certified := compare534 p (guard51 p guard)
  simpa only [at48, at27, Int.zero_add] using certified
theorem check51 (p : Pattern) : (!walkGuard soko2_2.board support p 48 27 .northEast || decide (bonus 48 p ≤ bonus 27 p)) = true :=
  check_of_implication _ _ (bound51 p)
theorem guard52 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 25 .northWest = true) : d4038 p = 1 := by
  change (!(p 48) && !false && !(true && true && false)) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound52 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 25 .northWest = true) : bonus 48 p ≤ bonus 25 p := by
  have certified := compare438 p (guard52 p guard)
  simpa only [at48, at25, Int.zero_add] using certified
theorem check52 (p : Pattern) : (!walkGuard soko2_2.board support p 48 25 .northWest || decide (bonus 48 p ≤ bonus 25 p)) = true :=
  check_of_implication _ _ (bound52 p)
theorem guard53 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 71 .southEast = true) : d4047 p = 1 := by
  change (!(p 48) && !(p 71) && !(true && false && (p 49))) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4042, d4047, h48, h49, h71] at guard ⊢
theorem bound53 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 71 .southEast = true) : bonus 48 p ≤ bonus 71 p := by
  have certified := compare541 p (guard53 p guard)
  simpa only [at48, at71, Int.zero_add] using certified
theorem check53 (p : Pattern) : (!walkGuard soko2_2.board support p 48 71 .southEast || decide (bonus 48 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound53 p)
theorem guard54 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 69 .southWest = true) : d4038 p = 1 := by
  change (!(p 48) && !false && !(true && false && false)) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound54 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 69 .southWest = true) : bonus 48 p ≤ bonus 69 p := by
  have certified := compare438 p (guard54 p guard)
  simpa only [at48, at69, Int.zero_add] using certified
theorem check54 (p : Pattern) : (!walkGuard soko2_2.board support p 48 69 .southWest || decide (bonus 48 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound54 p)
theorem guard55 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 27 .north = true) : d4040 p = 1 := by
  change (!(p 49) && !false && !false) = true at guard
  cases h49 : p 49
  all_goals simp [d0, d1, d4040, h49] at guard ⊢
theorem bound55 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 27 .north = true) : bonus 49 p ≤ bonus 27 p := by
  have certified := compare546 p (guard55 p guard)
  simpa only [at49, at27, Int.zero_add] using certified
theorem check55 (p : Pattern) : (!walkGuard soko2_2.board support p 49 27 .north || decide (bonus 49 p ≤ bonus 27 p)) = true :=
  check_of_implication _ _ (bound55 p)
theorem guard56 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 71 .south = true) : d4048 p = 1 := by
  change (!(p 49) && !(p 71) && !false) = true at guard
  cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4042, d4048, h49, h71] at guard ⊢
theorem bound56 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 71 .south = true) : bonus 49 p ≤ bonus 71 p := by
  have certified := compare551 p (guard56 p guard)
  simpa only [at49, at71, Int.zero_add] using certified
theorem check56 (p : Pattern) : (!walkGuard soko2_2.board support p 49 71 .south || decide (bonus 49 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound56 p)
theorem guard57 (p : Pattern) (guard : pushGuard support p 49 71 93 93 = true) : d4049 p = 1 := by
  change (!(p 49) && (!true || (p 71)) && !false && (!false || false)) = true at guard
  cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4041, d4049, h49, h71] at guard ⊢
theorem bound57 (p : Pattern) (guard : pushGuard support p 49 71 93 93 = true) : bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder 93 - Generated.soko2_2Potential.boulder 71 + bonus 71 (change p 71 (some 93)) := by
  have certified := compare557 p (guard57 p guard)
  change d484 p ≤ (0 : Int) + d488 (change p 71 (some 93))
  have normalized := agree488 _ _ (change_representative support p 71 (some 93) 10000 dummy_outside)
  rw [normalized]
  change d484 p ≤ (0 : Int) + d488 (change p 71 none)
  rw [sub1031]
  exact certified
theorem check57 (p : Pattern) : (!pushGuard support p 49 71 93 93 || decide (bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder 93 - Generated.soko2_2Potential.boulder 71 + bonus 71 (change p 71 (some 93)))) = true :=
  check_of_implication _ _ (bound57 p)
theorem guard58 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 50 .east = true) : d4040 p = 1 := by
  change (!(p 49) && !false && !false) = true at guard
  cases h49 : p 49
  all_goals simp [d0, d1, d4040, h49] at guard ⊢
theorem bound58 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 50 .east = true) : bonus 49 p ≤ bonus 50 p := by
  have certified := compare546 p (guard58 p guard)
  simpa only [at49, at50, Int.zero_add] using certified
theorem check58 (p : Pattern) : (!walkGuard soko2_2.board support p 49 50 .east || decide (bonus 49 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound58 p)
theorem guard59 (p : Pattern) (guard : pushGuard support p 49 50 51 51 = true) : d4040 p = 1 := by
  change (!(p 49) && (!false || false) && !false && (!false || false)) = true at guard
  cases h49 : p 49
  all_goals simp [d0, d1, d4040, h49] at guard ⊢
theorem bound59 (p : Pattern) (guard : pushGuard support p 49 50 51 51 = true) : bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder 51 - Generated.soko2_2Potential.boulder 50 + bonus 50 (change p 50 (some 51)) := by
  have certified := compare562 p (guard59 p guard)
  change d484 p ≤ (1 : Int) + d312 (change p 50 (some 51))
  have normalized := agree312 _ _ (change_representative support p 50 (some 51) 10000 dummy_outside)
  rw [normalized]
  change d484 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check59 (p : Pattern) : (!pushGuard support p 49 50 51 51 || decide (bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder 51 - Generated.soko2_2Potential.boulder 50 + bonus 50 (change p 50 (some 51)))) = true :=
  check_of_implication _ _ (bound59 p)
theorem guard60 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 48 .west = true) : d4044 p = 1 := by
  change (!(p 49) && !(p 48) && !false) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49
  all_goals simp [d0, d1, d4040, d4044, h48, h49] at guard ⊢
theorem bound60 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 48 .west = true) : bonus 49 p ≤ bonus 48 p := by
  have certified := compare564 p (guard60 p guard)
  simpa only [at49, at48, Int.zero_add] using certified
theorem check60 (p : Pattern) : (!walkGuard soko2_2.board support p 49 48 .west || decide (bonus 49 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound60 p)
theorem guard61 (p : Pattern) (guard : pushGuard support p 49 48 47 47 = true) : d4045 p = 1 := by
  change (!(p 49) && (!true || (p 48)) && !false && (!false || false)) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49
  all_goals simp [d0, d1, d4040, d4045, h48, h49] at guard ⊢
theorem bound61 (p : Pattern) (guard : pushGuard support p 49 48 47 47 = true) : bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.boulder 48 + bonus 48 (change p 48 (some 47)) := by
  have certified := compare568 p (guard61 p guard)
  change d484 p ≤ (1 : Int) + d481 (change p 48 (some 47))
  have normalized := agree481 _ _ (change_representative support p 48 (some 47) 10000 dummy_outside)
  rw [normalized]
  change d484 p ≤ (1 : Int) + d481 (change p 48 none)
  rw [sub1201]
  exact certified
theorem check61 (p : Pattern) : (!pushGuard support p 49 48 47 47 || decide (bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.boulder 48 + bonus 48 (change p 48 (some 47)))) = true :=
  check_of_implication _ _ (bound61 p)
theorem guard62 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 28 .northEast = true) : d4040 p = 1 := by
  change (!(p 49) && !false && !(true && false && false)) = true at guard
  cases h49 : p 49
  all_goals simp [d0, d1, d4040, h49] at guard ⊢
theorem bound62 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 28 .northEast = true) : bonus 49 p ≤ bonus 28 p := by
  have certified := compare546 p (guard62 p guard)
  simpa only [at49, at28, Int.zero_add] using certified
theorem check62 (p : Pattern) : (!walkGuard soko2_2.board support p 49 28 .northEast || decide (bonus 49 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound62 p)
theorem guard63 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 70 .southWest = true) : d4052 p = 1 := by
  change (!(p 49) && !false && !(true && (p 71) && (p 48))) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4040, d4042, d4048, d4052, h48, h49, h71] at guard ⊢
theorem bound63 (p : Pattern) (guard : walkGuard soko2_2.board support p 49 70 .southWest = true) : bonus 49 p ≤ bonus 70 p := by
  have certified := compare573 p (guard63 p guard)
  simpa only [at49, at70, Int.zero_add] using certified
theorem check63 (p : Pattern) : (!walkGuard soko2_2.board support p 49 70 .southWest || decide (bonus 49 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound63 p)
theorem guard64 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 28 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound64 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 28 .north = true) : bonus 50 p ≤ bonus 28 p := by
  have certified := compare19 p (guard64 p guard)
  simpa only [at50, at28, Int.zero_add] using certified
theorem check64 (p : Pattern) : (!walkGuard soko2_2.board support p 50 28 .north || decide (bonus 50 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound64 p)
theorem guard65 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 51 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound65 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 51 .east = true) : bonus 50 p ≤ bonus 51 p := by
  have certified := compare19 p (guard65 p guard)
  simpa only [at50, at51, Int.zero_add] using certified
theorem check65 (p : Pattern) : (!walkGuard soko2_2.board support p 50 51 .east || decide (bonus 50 p ≤ bonus 51 p)) = true :=
  check_of_implication _ _ (bound65 p)
theorem guard66 (p : Pattern) (guard : pushGuard support p 50 51 52 52 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound66 (p : Pattern) (guard : pushGuard support p 50 51 52 52 = true) : bonus 50 p ≤ 1 + Generated.soko2_2Potential.boulder 52 - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some 52)) := by
  have certified := compare20 p (guard66 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 51 (some 52))
  have normalized := agree312 _ _ (change_representative support p 51 (some 52) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check66 (p : Pattern) : (!pushGuard support p 50 51 52 52 || decide (bonus 50 p ≤ 1 + Generated.soko2_2Potential.boulder 52 - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some 52)))) = true :=
  check_of_implication _ _ (bound66 p)
theorem guard67 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 49 .west = true) : d4040 p = 1 := by
  change (!false && !(p 49) && !false) = true at guard
  cases h49 : p 49
  all_goals simp [d0, d1, d4040, h49] at guard ⊢
theorem bound67 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 49 .west = true) : bonus 50 p ≤ bonus 49 p := by
  have certified := compare10 p (guard67 p guard)
  simpa only [at50, at49, Int.zero_add] using certified
theorem check67 (p : Pattern) : (!walkGuard soko2_2.board support p 50 49 .west || decide (bonus 50 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound67 p)
theorem guard68 (p : Pattern) (guard : pushGuard support p 50 49 48 48 = true) : d4046 p = 1 := by
  change (!false && (!true || (p 49)) && !(p 48) && (!(p 48) || false)) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49
  all_goals simp [d0, d1, d4039, d4046, h48, h49] at guard ⊢
theorem bound68 (p : Pattern) (guard : pushGuard support p 50 49 48 48 = true) : bonus 50 p ≤ 1 + Generated.soko2_2Potential.boulder 48 - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some 48)) := by
  have certified := compare575 p (guard68 p guard)
  change d312 p ≤ (1 : Int) + d484 (change p 49 (some 48))
  have normalized := agree484 _ _ (change_representative support p 49 (some 48) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d484 (change p 49 (some 48))
  rw [sub1300]
  exact certified
theorem check68 (p : Pattern) : (!pushGuard support p 50 49 48 48 || decide (bonus 50 p ≤ 1 + Generated.soko2_2Potential.boulder 48 - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some 48)))) = true :=
  check_of_implication _ _ (bound68 p)
theorem guard69 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 29 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound69 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 29 .northEast = true) : bonus 50 p ≤ bonus 29 p := by
  have certified := compare19 p (guard69 p guard)
  simpa only [at50, at29, Int.zero_add] using certified
theorem check69 (p : Pattern) : (!walkGuard soko2_2.board support p 50 29 .northEast || decide (bonus 50 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound69 p)
theorem guard70 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 27 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 49))) = true at guard
  cases h49 : p 49
  all_goals simp [d1, h49] at guard ⊢
theorem bound70 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 27 .northWest = true) : bonus 50 p ≤ bonus 27 p := by
  have certified := compare19 p (guard70 p guard)
  simpa only [at50, at27, Int.zero_add] using certified
theorem check70 (p : Pattern) : (!walkGuard soko2_2.board support p 50 27 .northWest || decide (bonus 50 p ≤ bonus 27 p)) = true :=
  check_of_implication _ _ (bound70 p)
theorem guard71 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 73 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound71 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 73 .southEast = true) : bonus 50 p ≤ bonus 73 p := by
  have certified := compare19 p (guard71 p guard)
  simpa only [at50, at73, Int.zero_add] using certified
theorem check71 (p : Pattern) : (!walkGuard soko2_2.board support p 50 73 .southEast || decide (bonus 50 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound71 p)
end NetHack.Sokoban22Refined85
