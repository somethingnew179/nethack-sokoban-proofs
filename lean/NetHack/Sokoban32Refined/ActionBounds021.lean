import NetHack.Sokoban32Refined.ActionBounds020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard504 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 157 .southWest = true) : d841 p = 1 := by
  change (!(p 132) && !false && !(true && (p 158) && false)) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d841, h132, h158] at guard ⊢
theorem bound504 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 157 .southWest = true) : bonus 132 p ≤ bonus 157 p := by
  have certified := compare2785 p (guard504 p guard)
  simpa only [at132, at157, Int.zero_add] using certified
theorem check504 (p : Pattern) : (!walkGuard soko3_2.board support p 132 157 .southWest || decide (bonus 132 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound504 p)
theorem guard505 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 159 .south = true) : d1174 p = 1 := by
  change (!(p 133) && !(p 159) && !false) = true at guard
  cases h133 : p 133 <;> cases h159 : p 159
  all_goals simp [d0, d1, d1167, d1174, h133, h159] at guard ⊢
theorem bound505 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 159 .south = true) : bonus 133 p ≤ bonus 159 p := by
  have certified := compare2973 p (guard505 p guard)
  simpa only [at133, at159, Int.zero_add] using certified
theorem check505 (p : Pattern) : (!walkGuard soko3_2.board support p 133 159 .south || decide (bonus 133 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound505 p)
theorem guard506 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 134 .east = true) : d984 p = 1 := by
  change (!(p 133) && !(p 134) && !false) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d915, d984, h133, h134] at guard ⊢
theorem bound506 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 134 .east = true) : bonus 133 p ≤ bonus 134 p := by
  have certified := compare3058 p (guard506 p guard)
  simpa only [at133, at134, Int.zero_add] using certified
theorem check506 (p : Pattern) : (!walkGuard soko3_2.board support p 133 134 .east || decide (bonus 133 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound506 p)
theorem guard507 (p : Pattern) (guard : pushGuard support p 133 134 135 135 = true) : d1175 p = 1 := by
  change (!(p 133) && (!true || (p 134)) && !false && (!false || false)) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d914, d1175, h133, h134] at guard ⊢
theorem bound507 (p : Pattern) (guard : pushGuard support p 133 134 135 135 = true) : bonus 133 p ≤ 1 + Generated.soko3_2Potential.boulder 135 - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some 135)) := by
  have certified := compare3147 p (guard507 p guard)
  change d327 p ≤ (0 : Int) + d388 (change p 134 (some 135))
  have normalized := agree388 _ _ (change_representative support p 134 (some 135) 10000 dummy_outside)
  rw [normalized]
  change d327 p ≤ (0 : Int) + d388 (change p 134 none)
  rw [sub1780]
  exact certified
theorem check507 (p : Pattern) : (!pushGuard support p 133 134 135 135 || decide (bonus 133 p ≤ 1 + Generated.soko3_2Potential.boulder 135 - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some 135)))) = true :=
  check_of_implication _ _ (bound507 p)
theorem guard508 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 132 .west = true) : d912 p = 1 := by
  change (!(p 133) && !(p 132) && !false) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d910, d912, h132, h133] at guard ⊢
theorem bound508 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 132 .west = true) : bonus 133 p ≤ bonus 132 p := by
  have certified := compare3211 p (guard508 p guard)
  simpa only [at133, at132, Int.zero_add] using certified
theorem check508 (p : Pattern) : (!walkGuard soko3_2.board support p 133 132 .west || decide (bonus 133 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound508 p)
theorem guard509 (p : Pattern) (guard : pushGuard support p 133 132 131 131 = true) : d1132 p = 1 := by
  change (!(p 133) && (!true || (p 132)) && !false && (!false || false)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d910, d1132, h132, h133] at guard ⊢
theorem bound509 (p : Pattern) (guard : pushGuard support p 133 132 131 131 = true) : bonus 133 p ≤ 1 + Generated.soko3_2Potential.boulder 131 - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some 131)) := by
  have certified := compare3268 p (guard509 p guard)
  change d327 p ≤ (1 : Int) + d292 (change p 132 (some 131))
  have normalized := agree292 _ _ (change_representative support p 132 (some 131) 10000 dummy_outside)
  rw [normalized]
  change d327 p ≤ (1 : Int) + d292 (change p 132 none)
  rw [sub1866]
  exact certified
theorem check509 (p : Pattern) : (!pushGuard support p 133 132 131 131 || decide (bonus 133 p ≤ 1 + Generated.soko3_2Potential.boulder 131 - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some 131)))) = true :=
  check_of_implication _ _ (bound509 p)
theorem guard510 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 108 .northEast = true) : d984 p = 1 := by
  change (!(p 133) && !false && !(true && true && (p 134))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d915, d984, h133, h134] at guard ⊢
theorem bound510 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 108 .northEast = true) : bonus 133 p ≤ bonus 108 p := by
  have certified := compare3367 p (guard510 p guard)
  simpa only [at133, at108, Int.zero_add] using certified
theorem check510 (p : Pattern) : (!walkGuard soko3_2.board support p 133 108 .northEast || decide (bonus 133 p ≤ bonus 108 p)) = true :=
  check_of_implication _ _ (bound510 p)
theorem guard511 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 106 .northWest = true) : d913 p = 1 := by
  change (!(p 133) && !(p 106) && !(true && true && (p 132))) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d910, d912, d913, h106, h132, h133] at guard ⊢
theorem bound511 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 106 .northWest = true) : bonus 133 p ≤ bonus 106 p := by
  have certified := compare3403 p (guard511 p guard)
  simpa only [at133, at106, Int.zero_add] using certified
theorem check511 (p : Pattern) : (!walkGuard soko3_2.board support p 133 106 .northWest || decide (bonus 133 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound511 p)
theorem guard512 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 160 .southEast = true) : d1242 p = 1 := by
  change (!(p 133) && !(p 160) && !(true && (p 159) && (p 134))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1240, d1241, d1242, h133, h134, h159, h160] at guard ⊢
theorem bound512 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 160 .southEast = true) : bonus 133 p ≤ bonus 160 p := by
  have certified := compare3511 p (guard512 p guard)
  simpa only [at133, at160, Int.zero_add] using certified
theorem check512 (p : Pattern) : (!walkGuard soko3_2.board support p 133 160 .southEast || decide (bonus 133 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound512 p)
theorem guard513 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 158 .southWest = true) : d1247 p = 1 := by
  change (!(p 133) && !(p 158) && !(true && (p 159) && (p 132))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d873, d1167, d1171, d1243, d1246, d1247, h132, h133, h158, h159] at guard ⊢
theorem bound513 (p : Pattern) (guard : walkGuard soko3_2.board support p 133 158 .southWest = true) : bonus 133 p ≤ bonus 158 p := by
  have certified := compare3642 p (guard513 p guard)
  simpa only [at133, at158, Int.zero_add] using certified
theorem check513 (p : Pattern) : (!walkGuard soko3_2.board support p 133 158 .southWest || decide (bonus 133 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound513 p)
theorem guard514 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 108 .north = true) : d915 p = 1 := by
  change (!(p 134) && !false && !false) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d915, h134] at guard ⊢
theorem bound514 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 108 .north = true) : bonus 134 p ≤ bonus 108 p := by
  have certified := compare3735 p (guard514 p guard)
  simpa only [at134, at108, Int.zero_add] using certified
theorem check514 (p : Pattern) : (!walkGuard soko3_2.board support p 134 108 .north || decide (bonus 134 p ≤ bonus 108 p)) = true :=
  check_of_implication _ _ (bound514 p)
theorem guard515 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 160 .south = true) : d1248 p = 1 := by
  change (!(p 134) && !(p 160) && !false) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1248, h134, h160] at guard ⊢
theorem bound515 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 160 .south = true) : bonus 134 p ≤ bonus 160 p := by
  have certified := compare3809 p (guard515 p guard)
  simpa only [at134, at160, Int.zero_add] using certified
theorem check515 (p : Pattern) : (!walkGuard soko3_2.board support p 134 160 .south || decide (bonus 134 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound515 p)
theorem guard516 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 135 .east = true) : d915 p = 1 := by
  change (!(p 134) && !false && !false) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d915, h134] at guard ⊢
theorem bound516 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 135 .east = true) : bonus 134 p ≤ bonus 135 p := by
  have certified := compare3735 p (guard516 p guard)
  simpa only [at134, at135, Int.zero_add] using certified
theorem check516 (p : Pattern) : (!walkGuard soko3_2.board support p 134 135 .east || decide (bonus 134 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound516 p)
theorem guard517 (p : Pattern) (guard : pushGuard support p 134 135 136 136 = true) : d915 p = 1 := by
  change (!(p 134) && (!false || false) && !false && (!false || false)) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d915, h134] at guard ⊢
theorem bound517 (p : Pattern) (guard : pushGuard support p 134 135 136 136 = true) : bonus 134 p ≤ 1 + Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some 136)) := by
  have certified := compare3735 p (guard517 p guard)
  change d388 p ≤ (0 : Int) + d134 (change p 135 (some 136))
  have normalized := agree134 _ _ (change_representative support p 135 (some 136) 10000 dummy_outside)
  rw [normalized]
  change d388 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check517 (p : Pattern) : (!pushGuard support p 134 135 136 136 || decide (bonus 134 p ≤ 1 + Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some 136)))) = true :=
  check_of_implication _ _ (bound517 p)
theorem guard518 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 133 .west = true) : d984 p = 1 := by
  change (!(p 134) && !(p 133) && !false) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d915, d984, h133, h134] at guard ⊢
theorem bound518 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 133 .west = true) : bonus 134 p ≤ bonus 133 p := by
  have certified := compare3894 p (guard518 p guard)
  simpa only [at134, at133, Int.zero_add] using certified
theorem check518 (p : Pattern) : (!walkGuard soko3_2.board support p 134 133 .west || decide (bonus 134 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound518 p)
theorem guard519 (p : Pattern) (guard : pushGuard support p 134 133 132 132 = true) : d1151 p = 1 := by
  change (!(p 134) && (!true || (p 133)) && !(p 132) && (!(p 132) || false)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d915, d1150, d1151, h132, h133, h134] at guard ⊢
theorem bound519 (p : Pattern) (guard : pushGuard support p 134 133 132 132 = true) : bonus 134 p ≤ 1 + Generated.soko3_2Potential.boulder 132 - Generated.soko3_2Potential.boulder 133 + bonus 133 (change p 133 (some 132)) := by
  have certified := compare3974 p (guard519 p guard)
  change d388 p ≤ (2 : Int) + d327 (change p 133 (some 132))
  have normalized := agree327 _ _ (change_representative support p 133 (some 132) 10000 dummy_outside)
  rw [normalized]
  change d388 p ≤ (2 : Int) + d327 (change p 133 (some 132))
  rw [sub1922]
  exact certified
theorem check519 (p : Pattern) : (!pushGuard support p 134 133 132 132 || decide (bonus 134 p ≤ 1 + Generated.soko3_2Potential.boulder 132 - Generated.soko3_2Potential.boulder 133 + bonus 133 (change p 133 (some 132)))) = true :=
  check_of_implication _ _ (bound519 p)
theorem guard520 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 109 .northEast = true) : d915 p = 1 := by
  change (!(p 134) && !false && !(true && false && false)) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d915, h134] at guard ⊢
theorem bound520 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 109 .northEast = true) : bonus 134 p ≤ bonus 109 p := by
  have certified := compare3735 p (guard520 p guard)
  simpa only [at134, at109, Int.zero_add] using certified
theorem check520 (p : Pattern) : (!walkGuard soko3_2.board support p 134 109 .northEast || decide (bonus 134 p ≤ bonus 109 p)) = true :=
  check_of_implication _ _ (bound520 p)
theorem guard521 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 161 .southEast = true) : d1249 p = 1 := by
  change (!(p 134) && !(p 161) && !(true && (p 160) && false)) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d985, d1249, h134, h160, h161] at guard ⊢
theorem bound521 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 161 .southEast = true) : bonus 134 p ≤ bonus 161 p := by
  have certified := compare4094 p (guard521 p guard)
  simpa only [at134, at161, Int.zero_add] using certified
theorem check521 (p : Pattern) : (!walkGuard soko3_2.board support p 134 161 .southEast || decide (bonus 134 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound521 p)
theorem guard522 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 159 .southWest = true) : d1254 p = 1 := by
  change (!(p 134) && !(p 159) && !(true && (p 160) && (p 133))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1167, d1240, d1250, d1253, d1254, h133, h134, h159, h160] at guard ⊢
theorem bound522 (p : Pattern) (guard : walkGuard soko3_2.board support p 134 159 .southWest = true) : bonus 134 p ≤ bonus 159 p := by
  have certified := compare4198 p (guard522 p guard)
  simpa only [at134, at159, Int.zero_add] using certified
theorem check522 (p : Pattern) : (!walkGuard soko3_2.board support p 134 159 .southWest || decide (bonus 134 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound522 p)
theorem guard523 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 109 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound523 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 109 .north = true) : bonus 135 p ≤ bonus 109 p := by
  have certified := compare0 p (guard523 p guard)
  simpa only [at135, at109, Int.zero_add] using certified
theorem check523 (p : Pattern) : (!walkGuard soko3_2.board support p 135 109 .north || decide (bonus 135 p ≤ bonus 109 p)) = true :=
  check_of_implication _ _ (bound523 p)
theorem guard524 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 161 .south = true) : d985 p = 1 := by
  change (!false && !(p 161) && !false) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound524 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 161 .south = true) : bonus 135 p ≤ bonus 161 p := by
  have certified := compare4300 p (guard524 p guard)
  simpa only [at135, at161, Int.zero_add] using certified
theorem check524 (p : Pattern) : (!walkGuard soko3_2.board support p 135 161 .south || decide (bonus 135 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound524 p)
theorem guard525 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 136 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound525 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 136 .east = true) : bonus 135 p ≤ bonus 136 p := by
  have certified := compare0 p (guard525 p guard)
  simpa only [at135, at136, Int.zero_add] using certified
theorem check525 (p : Pattern) : (!walkGuard soko3_2.board support p 135 136 .east || decide (bonus 135 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound525 p)
theorem guard526 (p : Pattern) (guard : pushGuard support p 135 136 137 137 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound526 (p : Pattern) (guard : pushGuard support p 135 136 137 137 = true) : bonus 135 p ≤ 1 + Generated.soko3_2Potential.boulder 137 - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some 137)) := by
  have certified := compare4301 p (guard526 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 136 (some 137))
  have normalized := agree134 _ _ (change_representative support p 136 (some 137) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check526 (p : Pattern) : (!pushGuard support p 135 136 137 137 || decide (bonus 135 p ≤ 1 + Generated.soko3_2Potential.boulder 137 - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some 137)))) = true :=
  check_of_implication _ _ (bound526 p)
theorem guard527 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 134 .west = true) : d915 p = 1 := by
  change (!false && !(p 134) && !false) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d915, h134] at guard ⊢
theorem bound527 (p : Pattern) (guard : walkGuard soko3_2.board support p 135 134 .west = true) : bonus 135 p ≤ bonus 134 p := by
  have certified := compare945 p (guard527 p guard)
  simpa only [at135, at134, Int.zero_add] using certified
theorem check527 (p : Pattern) : (!walkGuard soko3_2.board support p 135 134 .west || decide (bonus 135 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound527 p)
end NetHack.Sokoban32Refined
