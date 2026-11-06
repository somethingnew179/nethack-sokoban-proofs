import NetHack.Sokoban22Refined85.ActionBounds020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard504 (p : Pattern) (guard : pushGuard support p 144 166 188 188 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound504 (p : Pattern) (guard : pushGuard support p 144 166 188 188 = true) : bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder 188 - Generated.soko2_2Potential.boulder 166 + bonus 166 (change p 166 (some 188)) := by
  have certified := compare1087 p (guard504 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 166 (some 188))
  have normalized := agree0 _ _ (change_representative support p 166 (some 188) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check504 (p : Pattern) : (!pushGuard support p 144 166 188 188 || decide (bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder 188 - Generated.soko2_2Potential.boulder 166 + bonus 166 (change p 166 (some 188)))) = true :=
  check_of_implication _ _ (bound504 p)
theorem guard505 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 145 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound505 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 145 .east = true) : bonus 144 p ≤ bonus 145 p := by
  have certified := compare1086 p (guard505 p guard)
  simpa only [at144, at145, Int.zero_add] using certified
theorem check505 (p : Pattern) : (!walkGuard soko2_2.board support p 144 145 .east || decide (bonus 144 p ≤ bonus 145 p)) = true :=
  check_of_implication _ _ (bound505 p)
theorem guard506 (p : Pattern) (guard : pushGuard support p 144 145 146 146 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound506 (p : Pattern) (guard : pushGuard support p 144 145 146 146 = true) : bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some 146)) := by
  have certified := compare1087 p (guard506 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 145 (some 146))
  have normalized := agree0 _ _ (change_representative support p 145 (some 146) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check506 (p : Pattern) : (!pushGuard support p 144 145 146 146 || decide (bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some 146)))) = true :=
  check_of_implication _ _ (bound506 p)
theorem guard507 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 123 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound507 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 123 .northEast = true) : bonus 144 p ≤ bonus 123 p := by
  have certified := compare1086 p (guard507 p guard)
  simpa only [at144, at123, Int.zero_add] using certified
theorem check507 (p : Pattern) : (!walkGuard soko2_2.board support p 144 123 .northEast || decide (bonus 144 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound507 p)
theorem guard508 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 167 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound508 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 167 .southEast = true) : bonus 144 p ≤ bonus 167 p := by
  have certified := compare1086 p (guard508 p guard)
  simpa only [at144, at167, Int.zero_add] using certified
theorem check508 (p : Pattern) : (!walkGuard soko2_2.board support p 144 167 .southEast || decide (bonus 144 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound508 p)
theorem guard509 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 123 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound509 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 123 .north = true) : bonus 145 p ≤ bonus 123 p := by
  have certified := compare1086 p (guard509 p guard)
  simpa only [at145, at123, Int.zero_add] using certified
theorem check509 (p : Pattern) : (!walkGuard soko2_2.board support p 145 123 .north || decide (bonus 145 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound509 p)
theorem guard510 (p : Pattern) (guard : pushGuard support p 145 123 101 101 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound510 (p : Pattern) (guard : pushGuard support p 145 123 101 101 = true) : bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder 101 - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some 101)) := by
  have certified := compare1087 p (guard510 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 123 (some 101))
  have normalized := agree0 _ _ (change_representative support p 123 (some 101) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check510 (p : Pattern) : (!pushGuard support p 145 123 101 101 || decide (bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder 101 - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some 101)))) = true :=
  check_of_implication _ _ (bound510 p)
theorem guard511 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 167 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound511 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 167 .south = true) : bonus 145 p ≤ bonus 167 p := by
  have certified := compare1086 p (guard511 p guard)
  simpa only [at145, at167, Int.zero_add] using certified
theorem check511 (p : Pattern) : (!walkGuard soko2_2.board support p 145 167 .south || decide (bonus 145 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound511 p)
theorem guard512 (p : Pattern) (guard : pushGuard support p 145 167 189 189 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound512 (p : Pattern) (guard : pushGuard support p 145 167 189 189 = true) : bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder 189 - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some 189)) := by
  have certified := compare1087 p (guard512 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 167 (some 189))
  have normalized := agree0 _ _ (change_representative support p 167 (some 189) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check512 (p : Pattern) : (!pushGuard support p 145 167 189 189 || decide (bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder 189 - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some 189)))) = true :=
  check_of_implication _ _ (bound512 p)
theorem guard513 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 146 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound513 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 146 .east = true) : bonus 145 p ≤ bonus 146 p := by
  have certified := compare1086 p (guard513 p guard)
  simpa only [at145, at146, Int.zero_add] using certified
theorem check513 (p : Pattern) : (!walkGuard soko2_2.board support p 145 146 .east || decide (bonus 145 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound513 p)
theorem guard514 (p : Pattern) (guard : pushGuard support p 145 146 147 147 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound514 (p : Pattern) (guard : pushGuard support p 145 146 147 147 = true) : bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some 147)) := by
  have certified := compare1087 p (guard514 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 146 (some 147))
  have normalized := agree0 _ _ (change_representative support p 146 (some 147) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check514 (p : Pattern) : (!pushGuard support p 145 146 147 147 || decide (bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some 147)))) = true :=
  check_of_implication _ _ (bound514 p)
theorem guard515 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 144 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound515 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 144 .west = true) : bonus 145 p ≤ bonus 144 p := by
  have certified := compare1086 p (guard515 p guard)
  simpa only [at145, at144, Int.zero_add] using certified
theorem check515 (p : Pattern) : (!walkGuard soko2_2.board support p 145 144 .west || decide (bonus 145 p ≤ bonus 144 p)) = true :=
  check_of_implication _ _ (bound515 p)
theorem guard516 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 124 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound516 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 124 .northEast = true) : bonus 145 p ≤ bonus 124 p := by
  have certified := compare1086 p (guard516 p guard)
  simpa only [at145, at124, Int.zero_add] using certified
theorem check516 (p : Pattern) : (!walkGuard soko2_2.board support p 145 124 .northEast || decide (bonus 145 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound516 p)
theorem guard517 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 122 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound517 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 122 .northWest = true) : bonus 145 p ≤ bonus 122 p := by
  have certified := compare1086 p (guard517 p guard)
  simpa only [at145, at122, Int.zero_add] using certified
theorem check517 (p : Pattern) : (!walkGuard soko2_2.board support p 145 122 .northWest || decide (bonus 145 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound517 p)
theorem guard518 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 168 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound518 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 168 .southEast = true) : bonus 145 p ≤ bonus 168 p := by
  have certified := compare1086 p (guard518 p guard)
  simpa only [at145, at168, Int.zero_add] using certified
theorem check518 (p : Pattern) : (!walkGuard soko2_2.board support p 145 168 .southEast || decide (bonus 145 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound518 p)
theorem guard519 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 166 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound519 (p : Pattern) (guard : walkGuard soko2_2.board support p 145 166 .southWest = true) : bonus 145 p ≤ bonus 166 p := by
  have certified := compare1086 p (guard519 p guard)
  simpa only [at145, at166, Int.zero_add] using certified
theorem check519 (p : Pattern) : (!walkGuard soko2_2.board support p 145 166 .southWest || decide (bonus 145 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound519 p)
theorem guard520 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 124 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound520 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 124 .north = true) : bonus 146 p ≤ bonus 124 p := by
  have certified := compare1086 p (guard520 p guard)
  simpa only [at146, at124, Int.zero_add] using certified
theorem check520 (p : Pattern) : (!walkGuard soko2_2.board support p 146 124 .north || decide (bonus 146 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound520 p)
theorem guard521 (p : Pattern) (guard : pushGuard support p 146 124 102 102 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound521 (p : Pattern) (guard : pushGuard support p 146 124 102 102 = true) : bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some 102)) := by
  have certified := compare1087 p (guard521 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 124 (some 102))
  have normalized := agree0 _ _ (change_representative support p 124 (some 102) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check521 (p : Pattern) : (!pushGuard support p 146 124 102 102 || decide (bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some 102)))) = true :=
  check_of_implication _ _ (bound521 p)
theorem guard522 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 168 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound522 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 168 .south = true) : bonus 146 p ≤ bonus 168 p := by
  have certified := compare1086 p (guard522 p guard)
  simpa only [at146, at168, Int.zero_add] using certified
theorem check522 (p : Pattern) : (!walkGuard soko2_2.board support p 146 168 .south || decide (bonus 146 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound522 p)
theorem guard523 (p : Pattern) (guard : pushGuard support p 146 168 190 190 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound523 (p : Pattern) (guard : pushGuard support p 146 168 190 190 = true) : bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some 190)) := by
  have certified := compare1087 p (guard523 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 168 (some 190))
  have normalized := agree0 _ _ (change_representative support p 168 (some 190) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check523 (p : Pattern) : (!pushGuard support p 146 168 190 190 || decide (bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some 190)))) = true :=
  check_of_implication _ _ (bound523 p)
theorem guard524 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 147 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound524 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 147 .east = true) : bonus 146 p ≤ bonus 147 p := by
  have certified := compare1086 p (guard524 p guard)
  simpa only [at146, at147, Int.zero_add] using certified
theorem check524 (p : Pattern) : (!walkGuard soko2_2.board support p 146 147 .east || decide (bonus 146 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound524 p)
theorem guard525 (p : Pattern) (guard : pushGuard support p 146 147 148 148 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound525 (p : Pattern) (guard : pushGuard support p 146 147 148 148 = true) : bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some 148)) := by
  have certified := compare1087 p (guard525 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 147 (some 148))
  have normalized := agree0 _ _ (change_representative support p 147 (some 148) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check525 (p : Pattern) : (!pushGuard support p 146 147 148 148 || decide (bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some 148)))) = true :=
  check_of_implication _ _ (bound525 p)
theorem guard526 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 145 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound526 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 145 .west = true) : bonus 146 p ≤ bonus 145 p := by
  have certified := compare1086 p (guard526 p guard)
  simpa only [at146, at145, Int.zero_add] using certified
theorem check526 (p : Pattern) : (!walkGuard soko2_2.board support p 146 145 .west || decide (bonus 146 p ≤ bonus 145 p)) = true :=
  check_of_implication _ _ (bound526 p)
theorem guard527 (p : Pattern) (guard : pushGuard support p 146 145 144 144 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound527 (p : Pattern) (guard : pushGuard support p 146 145 144 144 = true) : bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder 144 - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some 144)) := by
  have certified := compare1087 p (guard527 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 145 (some 144))
  have normalized := agree0 _ _ (change_representative support p 145 (some 144) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check527 (p : Pattern) : (!pushGuard support p 146 145 144 144 || decide (bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder 144 - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some 144)))) = true :=
  check_of_implication _ _ (bound527 p)
end NetHack.Sokoban22Refined85
