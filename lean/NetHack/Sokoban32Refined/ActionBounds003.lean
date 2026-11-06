import NetHack.Sokoban32Refined.ActionBounds002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard72 (p : Pattern) (guard : walkGuard soko3_2.board support p 50 75 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound72 (p : Pattern) (guard : walkGuard soko3_2.board support p 50 75 .southWest = true) : bonus 50 p ≤ bonus 75 p := by
  have certified := compare103 p (guard72 p guard)
  simpa only [at50, at75, Int.zero_add] using certified
theorem check72 (p : Pattern) : (!walkGuard soko3_2.board support p 50 75 .southWest || decide (bonus 50 p ≤ bonus 75 p)) = true :=
  check_of_implication _ _ (bound72 p)
theorem guard73 (p : Pattern) (guard : walkGuard soko3_2.board support p 53 79 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound73 (p : Pattern) (guard : walkGuard soko3_2.board support p 53 79 .south = true) : bonus 53 p ≤ bonus 79 p := by
  have certified := compare0 p (guard73 p guard)
  simpa only [at53, at79, Int.zero_add] using certified
theorem check73 (p : Pattern) : (!walkGuard soko3_2.board support p 53 79 .south || decide (bonus 53 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound73 p)
theorem guard74 (p : Pattern) (guard : pushGuard support p 53 79 105 105 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound74 (p : Pattern) (guard : pushGuard support p 53 79 105 105 = true) : bonus 53 p ≤ 1 + Generated.soko3_2Potential.boulder 105 - Generated.soko3_2Potential.boulder 79 + bonus 79 (change p 79 (some 105)) := by
  have certified := compare104 p (guard74 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 79 (some 105))
  have normalized := agree134 _ _ (change_representative support p 79 (some 105) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check74 (p : Pattern) : (!pushGuard support p 53 79 105 105 || decide (bonus 53 p ≤ 1 + Generated.soko3_2Potential.boulder 105 - Generated.soko3_2Potential.boulder 79 + bonus 79 (change p 79 (some 105)))) = true :=
  check_of_implication _ _ (bound74 p)
theorem guard75 (p : Pattern) (guard : walkGuard soko3_2.board support p 53 54 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound75 (p : Pattern) (guard : walkGuard soko3_2.board support p 53 54 .east = true) : bonus 53 p ≤ bonus 54 p := by
  have certified := compare0 p (guard75 p guard)
  simpa only [at53, at54, Int.zero_add] using certified
theorem check75 (p : Pattern) : (!walkGuard soko3_2.board support p 53 54 .east || decide (bonus 53 p ≤ bonus 54 p)) = true :=
  check_of_implication _ _ (bound75 p)
theorem guard76 (p : Pattern) (guard : pushGuard support p 53 54 55 55 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound76 (p : Pattern) (guard : pushGuard support p 53 54 55 55 = true) : bonus 53 p ≤ 1 + Generated.soko3_2Potential.boulder 55 - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some 55)) := by
  have certified := compare104 p (guard76 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 54 (some 55))
  have normalized := agree134 _ _ (change_representative support p 54 (some 55) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check76 (p : Pattern) : (!pushGuard support p 53 54 55 55 || decide (bonus 53 p ≤ 1 + Generated.soko3_2Potential.boulder 55 - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some 55)))) = true :=
  check_of_implication _ _ (bound76 p)
theorem guard77 (p : Pattern) (guard : walkGuard soko3_2.board support p 53 28 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound77 (p : Pattern) (guard : walkGuard soko3_2.board support p 53 28 .northEast = true) : bonus 53 p ≤ bonus 28 p := by
  have certified := compare0 p (guard77 p guard)
  simpa only [at53, at28, Int.zero_add] using certified
theorem check77 (p : Pattern) : (!walkGuard soko3_2.board support p 53 28 .northEast || decide (bonus 53 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound77 p)
theorem guard78 (p : Pattern) (guard : walkGuard soko3_2.board support p 53 80 .southEast = true) : d827 p = 1 := by
  change (!false && !(p 80) && !(true && false && false)) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound78 (p : Pattern) (guard : walkGuard soko3_2.board support p 53 80 .southEast = true) : bonus 53 p ≤ bonus 80 p := by
  have certified := compare107 p (guard78 p guard)
  simpa only [at53, at80, Int.zero_add] using certified
theorem check78 (p : Pattern) : (!walkGuard soko3_2.board support p 53 80 .southEast || decide (bonus 53 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound78 p)
theorem guard79 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 28 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound79 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 28 .north = true) : bonus 54 p ≤ bonus 28 p := by
  have certified := compare0 p (guard79 p guard)
  simpa only [at54, at28, Int.zero_add] using certified
theorem check79 (p : Pattern) : (!walkGuard soko3_2.board support p 54 28 .north || decide (bonus 54 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound79 p)
theorem guard80 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 80 .south = true) : d827 p = 1 := by
  change (!false && !(p 80) && !false) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound80 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 80 .south = true) : bonus 54 p ≤ bonus 80 p := by
  have certified := compare107 p (guard80 p guard)
  simpa only [at54, at80, Int.zero_add] using certified
theorem check80 (p : Pattern) : (!walkGuard soko3_2.board support p 54 80 .south || decide (bonus 54 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound80 p)
theorem guard81 (p : Pattern) (guard : pushGuard support p 54 80 106 106 = true) : d830 p = 1 := by
  change (!false && (!true || (p 80)) && !(p 106) && (!(p 106) || false)) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106
  all_goals simp [d0, d1, d829, d830, h80, h106] at guard ⊢
theorem bound81 (p : Pattern) (guard : pushGuard support p 54 80 106 106 = true) : bonus 54 p ≤ 1 + Generated.soko3_2Potential.boulder 106 - Generated.soko3_2Potential.boulder 80 + bonus 80 (change p 80 (some 106)) := by
  have certified := compare190 p (guard81 p guard)
  change d134 p ≤ (1 : Int) + d173 (change p 80 (some 106))
  have normalized := agree173 _ _ (change_representative support p 80 (some 106) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d173 (change p 80 (some 106))
  rw [sub328]
  exact certified
theorem check81 (p : Pattern) : (!pushGuard support p 54 80 106 106 || decide (bonus 54 p ≤ 1 + Generated.soko3_2Potential.boulder 106 - Generated.soko3_2Potential.boulder 80 + bonus 80 (change p 80 (some 106)))) = true :=
  check_of_implication _ _ (bound81 p)
theorem guard82 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 55 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound82 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 55 .east = true) : bonus 54 p ≤ bonus 55 p := by
  have certified := compare0 p (guard82 p guard)
  simpa only [at54, at55, Int.zero_add] using certified
theorem check82 (p : Pattern) : (!walkGuard soko3_2.board support p 54 55 .east || decide (bonus 54 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound82 p)
theorem guard83 (p : Pattern) (guard : pushGuard support p 54 55 56 56 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound83 (p : Pattern) (guard : pushGuard support p 54 55 56 56 = true) : bonus 54 p ≤ 1 + Generated.soko3_2Potential.boulder 56 - Generated.soko3_2Potential.boulder 55 + bonus 55 (change p 55 (some 56)) := by
  have certified := compare104 p (guard83 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 55 (some 56))
  have normalized := agree134 _ _ (change_representative support p 55 (some 56) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check83 (p : Pattern) : (!pushGuard support p 54 55 56 56 || decide (bonus 54 p ≤ 1 + Generated.soko3_2Potential.boulder 56 - Generated.soko3_2Potential.boulder 55 + bonus 55 (change p 55 (some 56)))) = true :=
  check_of_implication _ _ (bound83 p)
theorem guard84 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 53 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound84 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 53 .west = true) : bonus 54 p ≤ bonus 53 p := by
  have certified := compare0 p (guard84 p guard)
  simpa only [at54, at53, Int.zero_add] using certified
theorem check84 (p : Pattern) : (!walkGuard soko3_2.board support p 54 53 .west || decide (bonus 54 p ≤ bonus 53 p)) = true :=
  check_of_implication _ _ (bound84 p)
theorem guard85 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 29 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound85 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 29 .northEast = true) : bonus 54 p ≤ bonus 29 p := by
  have certified := compare0 p (guard85 p guard)
  simpa only [at54, at29, Int.zero_add] using certified
theorem check85 (p : Pattern) : (!walkGuard soko3_2.board support p 54 29 .northEast || decide (bonus 54 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound85 p)
theorem guard86 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 79 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 80) && false)) = true at guard
  cases h80 : p 80
  all_goals simp [d1, h80] at guard ⊢
theorem bound86 (p : Pattern) (guard : walkGuard soko3_2.board support p 54 79 .southWest = true) : bonus 54 p ≤ bonus 79 p := by
  have certified := compare0 p (guard86 p guard)
  simpa only [at54, at79, Int.zero_add] using certified
theorem check86 (p : Pattern) : (!walkGuard soko3_2.board support p 54 79 .southWest || decide (bonus 54 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound86 p)
theorem guard87 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 29 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound87 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 29 .north = true) : bonus 55 p ≤ bonus 29 p := by
  have certified := compare0 p (guard87 p guard)
  simpa only [at55, at29, Int.zero_add] using certified
theorem check87 (p : Pattern) : (!walkGuard soko3_2.board support p 55 29 .north || decide (bonus 55 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound87 p)
theorem guard88 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 56 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound88 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 56 .east = true) : bonus 55 p ≤ bonus 56 p := by
  have certified := compare0 p (guard88 p guard)
  simpa only [at55, at56, Int.zero_add] using certified
theorem check88 (p : Pattern) : (!walkGuard soko3_2.board support p 55 56 .east || decide (bonus 55 p ≤ bonus 56 p)) = true :=
  check_of_implication _ _ (bound88 p)
theorem guard89 (p : Pattern) (guard : pushGuard support p 55 56 57 57 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound89 (p : Pattern) (guard : pushGuard support p 55 56 57 57 = true) : bonus 55 p ≤ 1 + Generated.soko3_2Potential.boulder 57 - Generated.soko3_2Potential.boulder 56 + bonus 56 (change p 56 (some 57)) := by
  have certified := compare104 p (guard89 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 56 (some 57))
  have normalized := agree134 _ _ (change_representative support p 56 (some 57) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check89 (p : Pattern) : (!pushGuard support p 55 56 57 57 || decide (bonus 55 p ≤ 1 + Generated.soko3_2Potential.boulder 57 - Generated.soko3_2Potential.boulder 56 + bonus 56 (change p 56 (some 57)))) = true :=
  check_of_implication _ _ (bound89 p)
theorem guard90 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 54 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound90 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 54 .west = true) : bonus 55 p ≤ bonus 54 p := by
  have certified := compare0 p (guard90 p guard)
  simpa only [at55, at54, Int.zero_add] using certified
theorem check90 (p : Pattern) : (!walkGuard soko3_2.board support p 55 54 .west || decide (bonus 55 p ≤ bonus 54 p)) = true :=
  check_of_implication _ _ (bound90 p)
theorem guard91 (p : Pattern) (guard : pushGuard support p 55 54 53 53 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound91 (p : Pattern) (guard : pushGuard support p 55 54 53 53 = true) : bonus 55 p ≤ 1 + Generated.soko3_2Potential.boulder 53 - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some 53)) := by
  have certified := compare104 p (guard91 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 54 (some 53))
  have normalized := agree134 _ _ (change_representative support p 54 (some 53) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check91 (p : Pattern) : (!pushGuard support p 55 54 53 53 || decide (bonus 55 p ≤ 1 + Generated.soko3_2Potential.boulder 53 - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some 53)))) = true :=
  check_of_implication _ _ (bound91 p)
theorem guard92 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 28 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound92 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 28 .northWest = true) : bonus 55 p ≤ bonus 28 p := by
  have certified := compare0 p (guard92 p guard)
  simpa only [at55, at28, Int.zero_add] using certified
theorem check92 (p : Pattern) : (!walkGuard soko3_2.board support p 55 28 .northWest || decide (bonus 55 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound92 p)
theorem guard93 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 80 .southWest = true) : d827 p = 1 := by
  change (!false && !(p 80) && !(true && true && false)) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound93 (p : Pattern) (guard : walkGuard soko3_2.board support p 55 80 .southWest = true) : bonus 55 p ≤ bonus 80 p := by
  have certified := compare107 p (guard93 p guard)
  simpa only [at55, at80, Int.zero_add] using certified
theorem check93 (p : Pattern) : (!walkGuard soko3_2.board support p 55 80 .southWest || decide (bonus 55 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound93 p)
theorem guard94 (p : Pattern) (guard : walkGuard soko3_2.board support p 56 57 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound94 (p : Pattern) (guard : walkGuard soko3_2.board support p 56 57 .east = true) : bonus 56 p ≤ bonus 57 p := by
  have certified := compare0 p (guard94 p guard)
  simpa only [at56, at57, Int.zero_add] using certified
theorem check94 (p : Pattern) : (!walkGuard soko3_2.board support p 56 57 .east || decide (bonus 56 p ≤ bonus 57 p)) = true :=
  check_of_implication _ _ (bound94 p)
theorem guard95 (p : Pattern) (guard : pushGuard support p 56 57 58 58 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound95 (p : Pattern) (guard : pushGuard support p 56 57 58 58 = true) : bonus 56 p ≤ 1 + Generated.soko3_2Potential.boulder 58 - Generated.soko3_2Potential.boulder 57 + bonus 57 (change p 57 (some 58)) := by
  have certified := compare104 p (guard95 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 57 (some 58))
  have normalized := agree134 _ _ (change_representative support p 57 (some 58) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check95 (p : Pattern) : (!pushGuard support p 56 57 58 58 || decide (bonus 56 p ≤ 1 + Generated.soko3_2Potential.boulder 58 - Generated.soko3_2Potential.boulder 57 + bonus 57 (change p 57 (some 58)))) = true :=
  check_of_implication _ _ (bound95 p)
end NetHack.Sokoban32Refined
