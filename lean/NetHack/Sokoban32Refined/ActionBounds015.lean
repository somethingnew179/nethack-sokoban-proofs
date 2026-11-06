import NetHack.Sokoban32Refined.ActionBounds014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard360 (p : Pattern) (guard : pushGuard support p 109 135 161 161 = true) : d985 p = 1 := by
  change (!false && (!false || false) && !(p 161) && (!(p 161) || false)) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound360 (p : Pattern) (guard : pushGuard support p 109 135 161 161 = true) : bonus 109 p ≤ 1 + Generated.soko3_2Potential.boulder 161 - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some 161)) := by
  have certified := compare1348 p (guard360 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 135 (some 161))
  have normalized := agree134 _ _ (change_representative support p 135 (some 161) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 (some 161))
  rw [sub1031]
  exact certified
theorem check360 (p : Pattern) : (!pushGuard support p 109 135 161 161 || decide (bonus 109 p ≤ 1 + Generated.soko3_2Potential.boulder 161 - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some 161)))) = true :=
  check_of_implication _ _ (bound360 p)
theorem guard361 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 110 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound361 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 110 .east = true) : bonus 109 p ≤ bonus 110 p := by
  have certified := compare0 p (guard361 p guard)
  simpa only [at109, at110, Int.zero_add] using certified
theorem check361 (p : Pattern) : (!walkGuard soko3_2.board support p 109 110 .east || decide (bonus 109 p ≤ bonus 110 p)) = true :=
  check_of_implication _ _ (bound361 p)
theorem guard362 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 108 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound362 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 108 .west = true) : bonus 109 p ≤ bonus 108 p := by
  have certified := compare0 p (guard362 p guard)
  simpa only [at109, at108, Int.zero_add] using certified
theorem check362 (p : Pattern) : (!walkGuard soko3_2.board support p 109 108 .west || decide (bonus 109 p ≤ bonus 108 p)) = true :=
  check_of_implication _ _ (bound362 p)
theorem guard363 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 136 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound363 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 136 .southEast = true) : bonus 109 p ≤ bonus 136 p := by
  have certified := compare0 p (guard363 p guard)
  simpa only [at109, at136, Int.zero_add] using certified
theorem check363 (p : Pattern) : (!walkGuard soko3_2.board support p 109 136 .southEast || decide (bonus 109 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound363 p)
theorem guard364 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 134 .southWest = true) : d915 p = 1 := by
  change (!false && !(p 134) && !(true && false && false)) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d915, h134] at guard ⊢
theorem bound364 (p : Pattern) (guard : walkGuard soko3_2.board support p 109 134 .southWest = true) : bonus 109 p ≤ bonus 134 p := by
  have certified := compare945 p (guard364 p guard)
  simpa only [at109, at134, Int.zero_add] using certified
theorem check364 (p : Pattern) : (!walkGuard soko3_2.board support p 109 134 .southWest || decide (bonus 109 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound364 p)
theorem guard365 (p : Pattern) (guard : walkGuard soko3_2.board support p 110 136 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound365 (p : Pattern) (guard : walkGuard soko3_2.board support p 110 136 .south = true) : bonus 110 p ≤ bonus 136 p := by
  have certified := compare0 p (guard365 p guard)
  simpa only [at110, at136, Int.zero_add] using certified
theorem check365 (p : Pattern) : (!walkGuard soko3_2.board support p 110 136 .south || decide (bonus 110 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound365 p)
theorem guard366 (p : Pattern) (guard : pushGuard support p 110 136 162 162 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound366 (p : Pattern) (guard : pushGuard support p 110 136 162 162 = true) : bonus 110 p ≤ 1 + Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some 162)) := by
  have certified := compare0 p (guard366 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 136 (some 162))
  have normalized := agree134 _ _ (change_representative support p 136 (some 162) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check366 (p : Pattern) : (!pushGuard support p 110 136 162 162 || decide (bonus 110 p ≤ 1 + Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some 162)))) = true :=
  check_of_implication _ _ (bound366 p)
theorem guard367 (p : Pattern) (guard : walkGuard soko3_2.board support p 110 109 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound367 (p : Pattern) (guard : walkGuard soko3_2.board support p 110 109 .west = true) : bonus 110 p ≤ bonus 109 p := by
  have certified := compare0 p (guard367 p guard)
  simpa only [at110, at109, Int.zero_add] using certified
theorem check367 (p : Pattern) : (!walkGuard soko3_2.board support p 110 109 .west || decide (bonus 110 p ≤ bonus 109 p)) = true :=
  check_of_implication _ _ (bound367 p)
theorem guard368 (p : Pattern) (guard : pushGuard support p 110 109 108 108 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound368 (p : Pattern) (guard : pushGuard support p 110 109 108 108 = true) : bonus 110 p ≤ 1 + Generated.soko3_2Potential.boulder 108 - Generated.soko3_2Potential.boulder 109 + bonus 109 (change p 109 (some 108)) := by
  have certified := compare104 p (guard368 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 109 (some 108))
  have normalized := agree134 _ _ (change_representative support p 109 (some 108) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check368 (p : Pattern) : (!pushGuard support p 110 109 108 108 || decide (bonus 110 p ≤ 1 + Generated.soko3_2Potential.boulder 108 - Generated.soko3_2Potential.boulder 109 + bonus 109 (change p 109 (some 108)))) = true :=
  check_of_implication _ _ (bound368 p)
theorem guard369 (p : Pattern) (guard : walkGuard soko3_2.board support p 110 137 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound369 (p : Pattern) (guard : walkGuard soko3_2.board support p 110 137 .southEast = true) : bonus 110 p ≤ bonus 137 p := by
  have certified := compare0 p (guard369 p guard)
  simpa only [at110, at137, Int.zero_add] using certified
theorem check369 (p : Pattern) : (!walkGuard soko3_2.board support p 110 137 .southEast || decide (bonus 110 p ≤ bonus 137 p)) = true :=
  check_of_implication _ _ (bound369 p)
theorem guard370 (p : Pattern) (guard : walkGuard soko3_2.board support p 110 135 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound370 (p : Pattern) (guard : walkGuard soko3_2.board support p 110 135 .southWest = true) : bonus 110 p ≤ bonus 135 p := by
  have certified := compare0 p (guard370 p guard)
  simpa only [at110, at135, Int.zero_add] using certified
theorem check370 (p : Pattern) : (!walkGuard soko3_2.board support p 110 135 .southWest || decide (bonus 110 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound370 p)
theorem guard371 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 86 .north = true) : d854 p = 1 := by
  change (!(p 112) && !(p 86) && !false) = true at guard
  cases h86 : p 86 <;> cases h112 : p 112
  all_goals simp [d0, d1, d835, d854, h86, h112] at guard ⊢
theorem bound371 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 86 .north = true) : bonus 112 p ≤ bonus 86 p := by
  have certified := compare1363 p (guard371 p guard)
  simpa only [at112, at86, Int.zero_add] using certified
theorem check371 (p : Pattern) : (!walkGuard soko3_2.board support p 112 86 .north || decide (bonus 112 p ≤ bonus 86 p)) = true :=
  check_of_implication _ _ (bound371 p)
theorem guard372 (p : Pattern) (guard : pushGuard support p 112 86 60 60 = true) : d836 p = 1 := by
  change (!(p 112) && (!true || (p 86)) && !false && (!false || false)) = true at guard
  cases h86 : p 86 <;> cases h112 : p 112
  all_goals simp [d0, d1, d835, d836, h86, h112] at guard ⊢
theorem bound372 (p : Pattern) (guard : pushGuard support p 112 86 60 60 = true) : bonus 112 p ≤ 1 + Generated.soko3_2Potential.boulder 60 - Generated.soko3_2Potential.boulder 86 + bonus 86 (change p 86 (some 60)) := by
  have certified := compare1436 p (guard372 p guard)
  change d227 p ≤ (1 : Int) + d176 (change p 86 (some 60))
  have normalized := agree176 _ _ (change_representative support p 86 (some 60) 10000 dummy_outside)
  rw [normalized]
  change d227 p ≤ (1 : Int) + d176 (change p 86 none)
  rw [sub1122]
  exact certified
theorem check372 (p : Pattern) : (!pushGuard support p 112 86 60 60 || decide (bonus 112 p ≤ 1 + Generated.soko3_2Potential.boulder 60 - Generated.soko3_2Potential.boulder 86 + bonus 86 (change p 86 (some 60)))) = true :=
  check_of_implication _ _ (bound372 p)
theorem guard373 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 138 .south = true) : d1072 p = 1 := by
  change (!(p 112) && !(p 138) && !false) = true at guard
  cases h112 : p 112 <;> cases h138 : p 138
  all_goals simp [d0, d1, d857, d1072, h112, h138] at guard ⊢
theorem bound373 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 138 .south = true) : bonus 112 p ≤ bonus 138 p := by
  have certified := compare1513 p (guard373 p guard)
  simpa only [at112, at138, Int.zero_add] using certified
theorem check373 (p : Pattern) : (!walkGuard soko3_2.board support p 112 138 .south || decide (bonus 112 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound373 p)
theorem guard374 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 113 .east = true) : d868 p = 1 := by
  change (!(p 112) && !(p 113) && !false) = true at guard
  cases h112 : p 112 <;> cases h113 : p 113
  all_goals simp [d0, d1, d866, d868, h112, h113] at guard ⊢
theorem bound374 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 113 .east = true) : bonus 112 p ≤ bonus 113 p := by
  have certified := compare1544 p (guard374 p guard)
  simpa only [at112, at113, Int.zero_add] using certified
theorem check374 (p : Pattern) : (!walkGuard soko3_2.board support p 112 113 .east || decide (bonus 112 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound374 p)
theorem guard375 (p : Pattern) (guard : pushGuard support p 112 113 114 114 = true) : d1073 p = 1 := by
  change (!(p 112) && (!true || (p 113)) && !false && (!false || false)) = true at guard
  cases h112 : p 112 <;> cases h113 : p 113
  all_goals simp [d0, d1, d865, d1073, h112, h113] at guard ⊢
theorem bound375 (p : Pattern) (guard : pushGuard support p 112 113 114 114 = true) : bonus 112 p ≤ 1 + Generated.soko3_2Potential.boulder 114 - Generated.soko3_2Potential.boulder 113 + bonus 113 (change p 113 (some 114)) := by
  have certified := compare1577 p (guard375 p guard)
  change d227 p ≤ (1 : Int) + d255 (change p 113 (some 114))
  have normalized := agree255 _ _ (change_representative support p 113 (some 114) 10000 dummy_outside)
  rw [normalized]
  change d227 p ≤ (1 : Int) + d255 (change p 113 none)
  rw [sub1227]
  exact certified
theorem check375 (p : Pattern) : (!pushGuard support p 112 113 114 114 || decide (bonus 112 p ≤ 1 + Generated.soko3_2Potential.boulder 114 - Generated.soko3_2Potential.boulder 113 + bonus 113 (change p 113 (some 114)))) = true :=
  check_of_implication _ _ (bound375 p)
theorem guard376 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 139 .southEast = true) : d1094 p = 1 := by
  change (!(p 112) && !(p 139) && !(true && (p 138) && (p 113))) = true at guard
  cases h112 : p 112 <;> cases h113 : p 113 <;> cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1092, d1093, d1094, h112, h113, h138, h139] at guard ⊢
theorem bound376 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 139 .southEast = true) : bonus 112 p ≤ bonus 139 p := by
  have certified := compare1740 p (guard376 p guard)
  simpa only [at112, at139, Int.zero_add] using certified
theorem check376 (p : Pattern) : (!walkGuard soko3_2.board support p 112 139 .southEast || decide (bonus 112 p ≤ bonus 139 p)) = true :=
  check_of_implication _ _ (bound376 p)
theorem guard377 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 137 .southWest = true) : d1072 p = 1 := by
  change (!(p 112) && !false && !(true && (p 138) && true)) = true at guard
  cases h112 : p 112 <;> cases h138 : p 138
  all_goals simp [d0, d1, d857, d1072, h112, h138] at guard ⊢
theorem bound377 (p : Pattern) (guard : walkGuard soko3_2.board support p 112 137 .southWest = true) : bonus 112 p ≤ bonus 137 p := by
  have certified := compare1790 p (guard377 p guard)
  simpa only [at112, at137, Int.zero_add] using certified
theorem check377 (p : Pattern) : (!walkGuard soko3_2.board support p 112 137 .southWest || decide (bonus 112 p ≤ bonus 137 p)) = true :=
  check_of_implication _ _ (bound377 p)
theorem guard378 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 139 .south = true) : d1095 p = 1 := by
  change (!(p 113) && !(p 139) && !false) = true at guard
  cases h113 : p 113 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1095, h113, h139] at guard ⊢
theorem bound378 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 139 .south = true) : bonus 113 p ≤ bonus 139 p := by
  have certified := compare1866 p (guard378 p guard)
  simpa only [at113, at139, Int.zero_add] using certified
theorem check378 (p : Pattern) : (!walkGuard soko3_2.board support p 113 139 .south || decide (bonus 113 p ≤ bonus 139 p)) = true :=
  check_of_implication _ _ (bound378 p)
theorem guard379 (p : Pattern) (guard : pushGuard support p 113 139 165 165 = true) : d1096 p = 1 := by
  change (!(p 113) && (!true || (p 139)) && !false && (!false || false)) = true at guard
  cases h113 : p 113 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1087, d1096, h113, h139] at guard ⊢
theorem bound379 (p : Pattern) (guard : pushGuard support p 113 139 165 165 = true) : bonus 113 p ≤ 1 + Generated.soko3_2Potential.boulder 165 - Generated.soko3_2Potential.boulder 139 + bonus 139 (change p 139 (some 165)) := by
  have certified := compare1968 p (guard379 p guard)
  change d255 p ≤ (1 : Int) + d537 (change p 139 (some 165))
  have normalized := agree537 _ _ (change_representative support p 139 (some 165) 10000 dummy_outside)
  rw [normalized]
  change d255 p ≤ (1 : Int) + d537 (change p 139 none)
  rw [sub1356]
  exact certified
theorem check379 (p : Pattern) : (!pushGuard support p 113 139 165 165 || decide (bonus 113 p ≤ 1 + Generated.soko3_2Potential.boulder 165 - Generated.soko3_2Potential.boulder 139 + bonus 139 (change p 139 (some 165)))) = true :=
  check_of_implication _ _ (bound379 p)
theorem guard380 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 114 .east = true) : d866 p = 1 := by
  change (!(p 113) && !false && !false) = true at guard
  cases h113 : p 113
  all_goals simp [d0, d1, d866, h113] at guard ⊢
theorem bound380 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 114 .east = true) : bonus 113 p ≤ bonus 114 p := by
  have certified := compare2011 p (guard380 p guard)
  simpa only [at113, at114, Int.zero_add] using certified
theorem check380 (p : Pattern) : (!walkGuard soko3_2.board support p 113 114 .east || decide (bonus 113 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound380 p)
theorem guard381 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 112 .west = true) : d868 p = 1 := by
  change (!(p 113) && !(p 112) && !false) = true at guard
  cases h112 : p 112 <;> cases h113 : p 113
  all_goals simp [d0, d1, d866, d868, h112, h113] at guard ⊢
theorem bound381 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 112 .west = true) : bonus 113 p ≤ bonus 112 p := by
  have certified := compare2042 p (guard381 p guard)
  simpa only [at113, at112, Int.zero_add] using certified
theorem check381 (p : Pattern) : (!walkGuard soko3_2.board support p 113 112 .west || decide (bonus 113 p ≤ bonus 112 p)) = true :=
  check_of_implication _ _ (bound381 p)
theorem guard382 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 88 .northEast = true) : d866 p = 1 := by
  change (!(p 113) && !false && !(true && true && false)) = true at guard
  cases h113 : p 113
  all_goals simp [d0, d1, d866, h113] at guard ⊢
theorem bound382 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 88 .northEast = true) : bonus 113 p ≤ bonus 88 p := by
  have certified := compare2011 p (guard382 p guard)
  simpa only [at113, at88, Int.zero_add] using certified
theorem check382 (p : Pattern) : (!walkGuard soko3_2.board support p 113 88 .northEast || decide (bonus 113 p ≤ bonus 88 p)) = true :=
  check_of_implication _ _ (bound382 p)
theorem guard383 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 86 .northWest = true) : d869 p = 1 := by
  change (!(p 113) && !(p 86) && !(true && true && (p 112))) = true at guard
  cases h86 : p 86 <;> cases h112 : p 112 <;> cases h113 : p 113
  all_goals simp [d0, d1, d866, d868, d869, h86, h112, h113] at guard ⊢
theorem bound383 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 86 .northWest = true) : bonus 113 p ≤ bonus 86 p := by
  have certified := compare2057 p (guard383 p guard)
  simpa only [at113, at86, Int.zero_add] using certified
theorem check383 (p : Pattern) : (!walkGuard soko3_2.board support p 113 86 .northWest || decide (bonus 113 p ≤ bonus 86 p)) = true :=
  check_of_implication _ _ (bound383 p)
end NetHack.Sokoban32Refined
