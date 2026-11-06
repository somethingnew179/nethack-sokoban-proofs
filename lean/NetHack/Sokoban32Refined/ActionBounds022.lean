import NetHack.Sokoban32Refined.ActionBounds021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard528 (p : Pattern) (guard : pushGuard support p 135 134 133 133 = true) : d1175 p = 1 := by
  change (!false && (!true || (p 134)) && !(p 133) && (!(p 133) || false)) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d914, d1175, h133, h134] at guard ⊢
theorem bound528 (p : Pattern) (guard : pushGuard support p 135 134 133 133 = true) : bonus 135 p ≤ 1 + Generated.soko3_2Potential.boulder 133 - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some 133)) := by
  have certified := compare4469 p (guard528 p guard)
  change d134 p ≤ (2 : Int) + d388 (change p 134 (some 133))
  have normalized := agree388 _ _ (change_representative support p 134 (some 133) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d388 (change p 134 (some 133))
  rw [sub2016]
  exact certified
theorem check528 (p : Pattern) : (!pushGuard support p 135 134 133 133 || decide (bonus 135 p ≤ 1 + Generated.soko3_2Potential.boulder 133 - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some 133)))) = true :=
  check_of_implication _ _ (bound528 p)
theorem guard529 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 110 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound529 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 110 .northEast = true) : bonus 135 p ≤ bonus 110 p := by
  have certified := compare0 p (guard529 p guard)
  simpa only [at135, at110, Int.zero_add] using certified
theorem check529 (p : Pattern) : (!walkGuard soko3_2.board support p 135 110 .northEast || decide (bonus 135 p ≤ bonus 110 p)) = true :=
  check_of_implication _ _ (bound529 p)
theorem guard530 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 108 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 134))) = true at guard
  cases h134 : p 134
  all_goals simp [d1, h134] at guard ⊢
theorem bound530 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 108 .northWest = true) : bonus 135 p ≤ bonus 108 p := by
  have certified := compare0 p (guard530 p guard)
  simpa only [at135, at108, Int.zero_add] using certified
theorem check530 (p : Pattern) : (!walkGuard soko3_2.board support p 135 108 .northWest || decide (bonus 135 p ≤ bonus 108 p)) = true :=
  check_of_implication _ _ (bound530 p)
theorem guard531 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 162 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 161) && false)) = true at guard
  cases h161 : p 161
  all_goals simp [d1, h161] at guard ⊢
theorem bound531 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 162 .southEast = true) : bonus 135 p ≤ bonus 162 p := by
  have certified := compare0 p (guard531 p guard)
  simpa only [at135, at162, Int.zero_add] using certified
theorem check531 (p : Pattern) : (!walkGuard soko3_2.board support p 135 162 .southEast || decide (bonus 135 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound531 p)
theorem guard532 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 160 .southWest = true) : d1294 p = 1 := by
  change (!false && !(p 160) && !(true && (p 161) && (p 134))) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d917, d985, d1293, d1294, h134, h160, h161] at guard ⊢
theorem bound532 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 160 .southWest = true) : bonus 135 p ≤ bonus 160 p := by
  have certified := compare4601 p (guard532 p guard)
  simpa only [at135, at160, Int.zero_add] using certified
theorem check532 (p : Pattern) : (!walkGuard soko3_2.board support p 135 160 .southWest || decide (bonus 135 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound532 p)
theorem guard533 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 110 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound533 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 110 .north = true) : bonus 136 p ≤ bonus 110 p := by
  have certified := compare0 p (guard533 p guard)
  simpa only [at136, at110, Int.zero_add] using certified
theorem check533 (p : Pattern) : (!walkGuard soko3_2.board support p 136 110 .north || decide (bonus 136 p ≤ bonus 110 p)) = true :=
  check_of_implication _ _ (bound533 p)
theorem guard534 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 162 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound534 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 162 .south = true) : bonus 136 p ≤ bonus 162 p := by
  have certified := compare0 p (guard534 p guard)
  simpa only [at136, at162, Int.zero_add] using certified
theorem check534 (p : Pattern) : (!walkGuard soko3_2.board support p 136 162 .south || decide (bonus 136 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound534 p)
theorem guard535 (p : Pattern) (guard : pushGuard support p 136 162 188 188 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound535 (p : Pattern) (guard : pushGuard support p 136 162 188 188 = true) : bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder 188 - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some 188)) := by
  have certified := compare0 p (guard535 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 162 (some 188))
  have normalized := agree134 _ _ (change_representative support p 162 (some 188) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check535 (p : Pattern) : (!pushGuard support p 136 162 188 188 || decide (bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder 188 - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some 188)))) = true :=
  check_of_implication _ _ (bound535 p)
theorem guard536 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 137 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound536 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 137 .east = true) : bonus 136 p ≤ bonus 137 p := by
  have certified := compare0 p (guard536 p guard)
  simpa only [at136, at137, Int.zero_add] using certified
theorem check536 (p : Pattern) : (!walkGuard soko3_2.board support p 136 137 .east || decide (bonus 136 p ≤ bonus 137 p)) = true :=
  check_of_implication _ _ (bound536 p)
theorem guard537 (p : Pattern) (guard : pushGuard support p 136 137 138 138 = true) : d857 p = 1 := by
  change (!false && (!false || false) && !(p 138) && (!(p 138) || false)) = true at guard
  cases h138 : p 138
  all_goals simp [d0, d1, d857, h138] at guard ⊢
theorem bound537 (p : Pattern) (guard : pushGuard support p 136 137 138 138 = true) : bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder 138 - Generated.soko3_2Potential.boulder 137 + bonus 137 (change p 137 (some 138)) := by
  have certified := compare4749 p (guard537 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 137 (some 138))
  have normalized := agree134 _ _ (change_representative support p 137 (some 138) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 (some 138))
  rw [sub2150]
  exact certified
theorem check537 (p : Pattern) : (!pushGuard support p 136 137 138 138 || decide (bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder 138 - Generated.soko3_2Potential.boulder 137 + bonus 137 (change p 137 (some 138)))) = true :=
  check_of_implication _ _ (bound537 p)
theorem guard538 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 135 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound538 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 135 .west = true) : bonus 136 p ≤ bonus 135 p := by
  have certified := compare0 p (guard538 p guard)
  simpa only [at136, at135, Int.zero_add] using certified
theorem check538 (p : Pattern) : (!walkGuard soko3_2.board support p 136 135 .west || decide (bonus 136 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound538 p)
theorem guard539 (p : Pattern) (guard : pushGuard support p 136 135 134 134 = true) : d915 p = 1 := by
  change (!false && (!false || false) && !(p 134) && (!(p 134) || false)) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d915, h134] at guard ⊢
theorem bound539 (p : Pattern) (guard : pushGuard support p 136 135 134 134 = true) : bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder 134 - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some 134)) := by
  have certified := compare4882 p (guard539 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 135 (some 134))
  have normalized := agree134 _ _ (change_representative support p 135 (some 134) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 (some 134))
  rw [sub2274]
  exact certified
theorem check539 (p : Pattern) : (!pushGuard support p 136 135 134 134 || decide (bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder 134 - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some 134)))) = true :=
  check_of_implication _ _ (bound539 p)
theorem guard540 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 109 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound540 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 109 .northWest = true) : bonus 136 p ≤ bonus 109 p := by
  have certified := compare0 p (guard540 p guard)
  simpa only [at136, at109, Int.zero_add] using certified
theorem check540 (p : Pattern) : (!walkGuard soko3_2.board support p 136 109 .northWest || decide (bonus 136 p ≤ bonus 109 p)) = true :=
  check_of_implication _ _ (bound540 p)
theorem guard541 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 163 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound541 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 163 .southEast = true) : bonus 136 p ≤ bonus 163 p := by
  have certified := compare0 p (guard541 p guard)
  simpa only [at136, at163, Int.zero_add] using certified
theorem check541 (p : Pattern) : (!walkGuard soko3_2.board support p 136 163 .southEast || decide (bonus 136 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound541 p)
theorem guard542 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 161 .southWest = true) : d985 p = 1 := by
  change (!false && !(p 161) && !(true && false && false)) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound542 (p : Pattern) (guard : walkGuard soko3_2.board support p 136 161 .southWest = true) : bonus 136 p ≤ bonus 161 p := by
  have certified := compare4300 p (guard542 p guard)
  simpa only [at136, at161, Int.zero_add] using certified
theorem check542 (p : Pattern) : (!walkGuard soko3_2.board support p 136 161 .southWest || decide (bonus 136 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound542 p)
theorem guard543 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 163 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound543 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 163 .south = true) : bonus 137 p ≤ bonus 163 p := by
  have certified := compare0 p (guard543 p guard)
  simpa only [at137, at163, Int.zero_add] using certified
theorem check543 (p : Pattern) : (!walkGuard soko3_2.board support p 137 163 .south || decide (bonus 137 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound543 p)
theorem guard544 (p : Pattern) (guard : pushGuard support p 137 163 189 189 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound544 (p : Pattern) (guard : pushGuard support p 137 163 189 189 = true) : bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder 189 - Generated.soko3_2Potential.boulder 163 + bonus 163 (change p 163 (some 189)) := by
  have certified := compare0 p (guard544 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 163 (some 189))
  have normalized := agree134 _ _ (change_representative support p 163 (some 189) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check544 (p : Pattern) : (!pushGuard support p 137 163 189 189 || decide (bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder 189 - Generated.soko3_2Potential.boulder 163 + bonus 163 (change p 163 (some 189)))) = true :=
  check_of_implication _ _ (bound544 p)
theorem guard545 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 138 .east = true) : d857 p = 1 := by
  change (!false && !(p 138) && !false) = true at guard
  cases h138 : p 138
  all_goals simp [d0, d1, d857, h138] at guard ⊢
theorem bound545 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 138 .east = true) : bonus 137 p ≤ bonus 138 p := by
  have certified := compare4964 p (guard545 p guard)
  simpa only [at137, at138, Int.zero_add] using certified
theorem check545 (p : Pattern) : (!walkGuard soko3_2.board support p 137 138 .east || decide (bonus 137 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound545 p)
theorem guard546 (p : Pattern) (guard : pushGuard support p 137 138 139 139 = true) : d1365 p = 1 := by
  change (!false && (!true || (p 138)) && !(p 139) && (!(p 139) || false)) = true at guard
  cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1365, h138, h139] at guard ⊢
theorem bound546 (p : Pattern) (guard : pushGuard support p 137 138 139 139 = true) : bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder 139 - Generated.soko3_2Potential.boulder 138 + bonus 138 (change p 138 (some 139)) := by
  have certified := compare5159 p (guard546 p guard)
  change d134 p ≤ (3 : Int) + d455 (change p 138 (some 139))
  have normalized := agree455 _ _ (change_representative support p 138 (some 139) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (3 : Int) + d455 (change p 138 (some 139))
  rw [sub2384]
  exact certified
theorem check546 (p : Pattern) : (!pushGuard support p 137 138 139 139 || decide (bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder 139 - Generated.soko3_2Potential.boulder 138 + bonus 138 (change p 138 (some 139)))) = true :=
  check_of_implication _ _ (bound546 p)
theorem guard547 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 136 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound547 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 136 .west = true) : bonus 137 p ≤ bonus 136 p := by
  have certified := compare0 p (guard547 p guard)
  simpa only [at137, at136, Int.zero_add] using certified
theorem check547 (p : Pattern) : (!walkGuard soko3_2.board support p 137 136 .west || decide (bonus 137 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound547 p)
theorem guard548 (p : Pattern) (guard : pushGuard support p 137 136 135 135 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound548 (p : Pattern) (guard : pushGuard support p 137 136 135 135 = true) : bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder 135 - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some 135)) := by
  have certified := compare4301 p (guard548 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 136 (some 135))
  have normalized := agree134 _ _ (change_representative support p 136 (some 135) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check548 (p : Pattern) : (!pushGuard support p 137 136 135 135 || decide (bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder 135 - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some 135)))) = true :=
  check_of_implication _ _ (bound548 p)
theorem guard549 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 112 .northEast = true) : d1072 p = 1 := by
  change (!false && !(p 112) && !(true && true && (p 138))) = true at guard
  cases h112 : p 112 <;> cases h138 : p 138
  all_goals simp [d0, d1, d857, d1072, h112, h138] at guard ⊢
theorem bound549 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 112 .northEast = true) : bonus 137 p ≤ bonus 112 p := by
  have certified := compare5207 p (guard549 p guard)
  simpa only [at137, at112, Int.zero_add] using certified
theorem check549 (p : Pattern) : (!walkGuard soko3_2.board support p 137 112 .northEast || decide (bonus 137 p ≤ bonus 112 p)) = true :=
  check_of_implication _ _ (bound549 p)
theorem guard550 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 110 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound550 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 110 .northWest = true) : bonus 137 p ≤ bonus 110 p := by
  have certified := compare0 p (guard550 p guard)
  simpa only [at137, at110, Int.zero_add] using certified
theorem check550 (p : Pattern) : (!walkGuard soko3_2.board support p 137 110 .northWest || decide (bonus 137 p ≤ bonus 110 p)) = true :=
  check_of_implication _ _ (bound550 p)
theorem guard551 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 162 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound551 (p : Pattern) (guard : walkGuard soko3_2.board support p 137 162 .southWest = true) : bonus 137 p ≤ bonus 162 p := by
  have certified := compare0 p (guard551 p guard)
  simpa only [at137, at162, Int.zero_add] using certified
theorem check551 (p : Pattern) : (!walkGuard soko3_2.board support p 137 162 .southWest || decide (bonus 137 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound551 p)
end NetHack.Sokoban32Refined
