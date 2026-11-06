import NetHack.Sokoban22Refined85.ActionBounds017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard432 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 149 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound432 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 149 .southEast = true) : bonus 126 p ≤ bonus 149 p := by
  have certified := compare1086 p (guard432 p guard)
  simpa only [at126, at149, Int.zero_add] using certified
theorem check432 (p : Pattern) : (!walkGuard soko2_2.board support p 126 149 .southEast || decide (bonus 126 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound432 p)
theorem guard433 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 147 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound433 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 147 .southWest = true) : bonus 126 p ≤ bonus 147 p := by
  have certified := compare1086 p (guard433 p guard)
  simpa only [at126, at147, Int.zero_add] using certified
theorem check433 (p : Pattern) : (!walkGuard soko2_2.board support p 126 147 .southWest || decide (bonus 126 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound433 p)
theorem guard434 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 105 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound434 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 105 .north = true) : bonus 127 p ≤ bonus 105 p := by
  have certified := compare1086 p (guard434 p guard)
  simpa only [at127, at105, Int.zero_add] using certified
theorem check434 (p : Pattern) : (!walkGuard soko2_2.board support p 127 105 .north || decide (bonus 127 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound434 p)
theorem guard435 (p : Pattern) (guard : pushGuard support p 127 105 83 83 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound435 (p : Pattern) (guard : pushGuard support p 127 105 83 83 = true) : bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder 83 - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some 83)) := by
  have certified := compare1087 p (guard435 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 105 (some 83))
  have normalized := agree0 _ _ (change_representative support p 105 (some 83) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check435 (p : Pattern) : (!pushGuard support p 127 105 83 83 || decide (bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder 83 - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some 83)))) = true :=
  check_of_implication _ _ (bound435 p)
theorem guard436 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 149 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound436 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 149 .south = true) : bonus 127 p ≤ bonus 149 p := by
  have certified := compare1086 p (guard436 p guard)
  simpa only [at127, at149, Int.zero_add] using certified
theorem check436 (p : Pattern) : (!walkGuard soko2_2.board support p 127 149 .south || decide (bonus 127 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound436 p)
theorem guard437 (p : Pattern) (guard : pushGuard support p 127 149 171 171 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound437 (p : Pattern) (guard : pushGuard support p 127 149 171 171 = true) : bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some 171)) := by
  have certified := compare1087 p (guard437 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 149 (some 171))
  have normalized := agree0 _ _ (change_representative support p 149 (some 171) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check437 (p : Pattern) : (!pushGuard support p 127 149 171 171 || decide (bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some 171)))) = true :=
  check_of_implication _ _ (bound437 p)
theorem guard438 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 128 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound438 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 128 .east = true) : bonus 127 p ≤ bonus 128 p := by
  have certified := compare1086 p (guard438 p guard)
  simpa only [at127, at128, Int.zero_add] using certified
theorem check438 (p : Pattern) : (!walkGuard soko2_2.board support p 127 128 .east || decide (bonus 127 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound438 p)
theorem guard439 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 126 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound439 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 126 .west = true) : bonus 127 p ≤ bonus 126 p := by
  have certified := compare1086 p (guard439 p guard)
  simpa only [at127, at126, Int.zero_add] using certified
theorem check439 (p : Pattern) : (!walkGuard soko2_2.board support p 127 126 .west || decide (bonus 127 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound439 p)
theorem guard440 (p : Pattern) (guard : pushGuard support p 127 126 125 125 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound440 (p : Pattern) (guard : pushGuard support p 127 126 125 125 = true) : bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some 125)) := by
  have certified := compare1087 p (guard440 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 126 (some 125))
  have normalized := agree0 _ _ (change_representative support p 126 (some 125) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check440 (p : Pattern) : (!pushGuard support p 127 126 125 125 || decide (bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some 125)))) = true :=
  check_of_implication _ _ (bound440 p)
theorem guard441 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 106 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound441 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 106 .northEast = true) : bonus 127 p ≤ bonus 106 p := by
  have certified := compare1086 p (guard441 p guard)
  simpa only [at127, at106, Int.zero_add] using certified
theorem check441 (p : Pattern) : (!walkGuard soko2_2.board support p 127 106 .northEast || decide (bonus 127 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound441 p)
theorem guard442 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 104 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound442 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 104 .northWest = true) : bonus 127 p ≤ bonus 104 p := by
  have certified := compare1086 p (guard442 p guard)
  simpa only [at127, at104, Int.zero_add] using certified
theorem check442 (p : Pattern) : (!walkGuard soko2_2.board support p 127 104 .northWest || decide (bonus 127 p ≤ bonus 104 p)) = true :=
  check_of_implication _ _ (bound442 p)
theorem guard443 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 150 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound443 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 150 .southEast = true) : bonus 127 p ≤ bonus 150 p := by
  have certified := compare1086 p (guard443 p guard)
  simpa only [at127, at150, Int.zero_add] using certified
theorem check443 (p : Pattern) : (!walkGuard soko2_2.board support p 127 150 .southEast || decide (bonus 127 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound443 p)
theorem guard444 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 148 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound444 (p : Pattern) (guard : walkGuard soko2_2.board support p 127 148 .southWest = true) : bonus 127 p ≤ bonus 148 p := by
  have certified := compare1086 p (guard444 p guard)
  simpa only [at127, at148, Int.zero_add] using certified
theorem check444 (p : Pattern) : (!walkGuard soko2_2.board support p 127 148 .southWest || decide (bonus 127 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound444 p)
theorem guard445 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 106 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound445 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 106 .north = true) : bonus 128 p ≤ bonus 106 p := by
  have certified := compare1086 p (guard445 p guard)
  simpa only [at128, at106, Int.zero_add] using certified
theorem check445 (p : Pattern) : (!walkGuard soko2_2.board support p 128 106 .north || decide (bonus 128 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound445 p)
theorem guard446 (p : Pattern) (guard : pushGuard support p 128 106 84 84 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound446 (p : Pattern) (guard : pushGuard support p 128 106 84 84 = true) : bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder 84 - Generated.soko2_2Potential.boulder 106 + bonus 106 (change p 106 (some 84)) := by
  have certified := compare1087 p (guard446 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 106 (some 84))
  have normalized := agree0 _ _ (change_representative support p 106 (some 84) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check446 (p : Pattern) : (!pushGuard support p 128 106 84 84 || decide (bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder 84 - Generated.soko2_2Potential.boulder 106 + bonus 106 (change p 106 (some 84)))) = true :=
  check_of_implication _ _ (bound446 p)
theorem guard447 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 150 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound447 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 150 .south = true) : bonus 128 p ≤ bonus 150 p := by
  have certified := compare1086 p (guard447 p guard)
  simpa only [at128, at150, Int.zero_add] using certified
theorem check447 (p : Pattern) : (!walkGuard soko2_2.board support p 128 150 .south || decide (bonus 128 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound447 p)
theorem guard448 (p : Pattern) (guard : pushGuard support p 128 150 172 172 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound448 (p : Pattern) (guard : pushGuard support p 128 150 172 172 = true) : bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder 172 - Generated.soko2_2Potential.boulder 150 + bonus 150 (change p 150 (some 172)) := by
  have certified := compare1087 p (guard448 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 150 (some 172))
  have normalized := agree0 _ _ (change_representative support p 150 (some 172) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check448 (p : Pattern) : (!pushGuard support p 128 150 172 172 || decide (bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder 172 - Generated.soko2_2Potential.boulder 150 + bonus 150 (change p 150 (some 172)))) = true :=
  check_of_implication _ _ (bound448 p)
theorem guard449 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 127 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound449 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 127 .west = true) : bonus 128 p ≤ bonus 127 p := by
  have certified := compare1086 p (guard449 p guard)
  simpa only [at128, at127, Int.zero_add] using certified
theorem check449 (p : Pattern) : (!walkGuard soko2_2.board support p 128 127 .west || decide (bonus 128 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound449 p)
theorem guard450 (p : Pattern) (guard : pushGuard support p 128 127 126 126 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound450 (p : Pattern) (guard : pushGuard support p 128 127 126 126 = true) : bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some 126)) := by
  have certified := compare1087 p (guard450 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 127 (some 126))
  have normalized := agree0 _ _ (change_representative support p 127 (some 126) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check450 (p : Pattern) : (!pushGuard support p 128 127 126 126 || decide (bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some 126)))) = true :=
  check_of_implication _ _ (bound450 p)
theorem guard451 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 105 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound451 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 105 .northWest = true) : bonus 128 p ≤ bonus 105 p := by
  have certified := compare1086 p (guard451 p guard)
  simpa only [at128, at105, Int.zero_add] using certified
theorem check451 (p : Pattern) : (!walkGuard soko2_2.board support p 128 105 .northWest || decide (bonus 128 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound451 p)
theorem guard452 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 149 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound452 (p : Pattern) (guard : walkGuard soko2_2.board support p 128 149 .southWest = true) : bonus 128 p ≤ bonus 149 p := by
  have certified := compare1086 p (guard452 p guard)
  simpa only [at128, at149, Int.zero_add] using certified
theorem check452 (p : Pattern) : (!walkGuard soko2_2.board support p 128 149 .southWest || decide (bonus 128 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound452 p)
theorem guard453 (p : Pattern) (guard : walkGuard soko2_2.board support p 133 111 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound453 (p : Pattern) (guard : walkGuard soko2_2.board support p 133 111 .north = true) : bonus 133 p ≤ bonus 111 p := by
  have certified := compare0 p (guard453 p guard)
  simpa only [at133, at111, Int.zero_add] using certified
theorem check453 (p : Pattern) : (!walkGuard soko2_2.board support p 133 111 .north || decide (bonus 133 p ≤ bonus 111 p)) = true :=
  check_of_implication _ _ (bound453 p)
theorem guard454 (p : Pattern) (guard : pushGuard support p 133 111 89 89 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound454 (p : Pattern) (guard : pushGuard support p 133 111 89 89 = true) : bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder 89 - Generated.soko2_2Potential.boulder 111 + bonus 111 (change p 111 (some 89)) := by
  have certified := compare1 p (guard454 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 111 (some 89))
  have normalized := agree267 _ _ (change_representative support p 111 (some 89) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check454 (p : Pattern) : (!pushGuard support p 133 111 89 89 || decide (bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder 89 - Generated.soko2_2Potential.boulder 111 + bonus 111 (change p 111 (some 89)))) = true :=
  check_of_implication _ _ (bound454 p)
theorem guard455 (p : Pattern) (guard : walkGuard soko2_2.board support p 133 155 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound455 (p : Pattern) (guard : walkGuard soko2_2.board support p 133 155 .south = true) : bonus 133 p ≤ bonus 155 p := by
  have certified := compare0 p (guard455 p guard)
  simpa only [at133, at155, Int.zero_add] using certified
theorem check455 (p : Pattern) : (!walkGuard soko2_2.board support p 133 155 .south || decide (bonus 133 p ≤ bonus 155 p)) = true :=
  check_of_implication _ _ (bound455 p)
end NetHack.Sokoban22Refined85
