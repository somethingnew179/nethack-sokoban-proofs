import NetHack.Sokoban22Refined85.ActionBounds018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard456 (p : Pattern) (guard : pushGuard support p 133 155 177 177 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound456 (p : Pattern) (guard : pushGuard support p 133 155 177 177 = true) : bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder 177 - Generated.soko2_2Potential.boulder 155 + bonus 155 (change p 155 (some 177)) := by
  have certified := compare1 p (guard456 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 155 (some 177))
  have normalized := agree267 _ _ (change_representative support p 155 (some 177) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check456 (p : Pattern) : (!pushGuard support p 133 155 177 177 || decide (bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder 177 - Generated.soko2_2Potential.boulder 155 + bonus 155 (change p 155 (some 177)))) = true :=
  check_of_implication _ _ (bound456 p)
theorem guard457 (p : Pattern) (guard : walkGuard soko2_2.board support p 133 134 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound457 (p : Pattern) (guard : walkGuard soko2_2.board support p 133 134 .east = true) : bonus 133 p ≤ bonus 134 p := by
  have certified := compare0 p (guard457 p guard)
  simpa only [at133, at134, Int.zero_add] using certified
theorem check457 (p : Pattern) : (!walkGuard soko2_2.board support p 133 134 .east || decide (bonus 133 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound457 p)
theorem guard458 (p : Pattern) (guard : pushGuard support p 133 134 135 135 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound458 (p : Pattern) (guard : pushGuard support p 133 134 135 135 = true) : bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder 135 - Generated.soko2_2Potential.boulder 134 + bonus 134 (change p 134 (some 135)) := by
  have certified := compare0 p (guard458 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 134 (some 135))
  have normalized := agree267 _ _ (change_representative support p 134 (some 135) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check458 (p : Pattern) : (!pushGuard support p 133 134 135 135 || decide (bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder 135 - Generated.soko2_2Potential.boulder 134 + bonus 134 (change p 134 (some 135)))) = true :=
  check_of_implication _ _ (bound458 p)
theorem guard459 (p : Pattern) (guard : walkGuard soko2_2.board support p 133 156 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound459 (p : Pattern) (guard : walkGuard soko2_2.board support p 133 156 .southEast = true) : bonus 133 p ≤ bonus 156 p := by
  have certified := compare0 p (guard459 p guard)
  simpa only [at133, at156, Int.zero_add] using certified
theorem check459 (p : Pattern) : (!walkGuard soko2_2.board support p 133 156 .southEast || decide (bonus 133 p ≤ bonus 156 p)) = true :=
  check_of_implication _ _ (bound459 p)
theorem guard460 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 156 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound460 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 156 .south = true) : bonus 134 p ≤ bonus 156 p := by
  have certified := compare0 p (guard460 p guard)
  simpa only [at134, at156, Int.zero_add] using certified
theorem check460 (p : Pattern) : (!walkGuard soko2_2.board support p 134 156 .south || decide (bonus 134 p ≤ bonus 156 p)) = true :=
  check_of_implication _ _ (bound460 p)
theorem guard461 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 135 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound461 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 135 .east = true) : bonus 134 p ≤ bonus 135 p := by
  have certified := compare0 p (guard461 p guard)
  simpa only [at134, at135, Int.zero_add] using certified
theorem check461 (p : Pattern) : (!walkGuard soko2_2.board support p 134 135 .east || decide (bonus 134 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound461 p)
theorem guard462 (p : Pattern) (guard : pushGuard support p 134 135 136 136 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound462 (p : Pattern) (guard : pushGuard support p 134 135 136 136 = true) : bonus 134 p ≤ 1 + Generated.soko2_2Potential.boulder 136 - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some 136)) := by
  have certified := compare0 p (guard462 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 135 (some 136))
  have normalized := agree267 _ _ (change_representative support p 135 (some 136) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check462 (p : Pattern) : (!pushGuard support p 134 135 136 136 || decide (bonus 134 p ≤ 1 + Generated.soko2_2Potential.boulder 136 - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some 136)))) = true :=
  check_of_implication _ _ (bound462 p)
theorem guard463 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 133 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound463 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 133 .west = true) : bonus 134 p ≤ bonus 133 p := by
  have certified := compare0 p (guard463 p guard)
  simpa only [at134, at133, Int.zero_add] using certified
theorem check463 (p : Pattern) : (!walkGuard soko2_2.board support p 134 133 .west || decide (bonus 134 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound463 p)
theorem guard464 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 113 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound464 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 113 .northEast = true) : bonus 134 p ≤ bonus 113 p := by
  have certified := compare0 p (guard464 p guard)
  simpa only [at134, at113, Int.zero_add] using certified
theorem check464 (p : Pattern) : (!walkGuard soko2_2.board support p 134 113 .northEast || decide (bonus 134 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound464 p)
theorem guard465 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 111 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound465 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 111 .northWest = true) : bonus 134 p ≤ bonus 111 p := by
  have certified := compare0 p (guard465 p guard)
  simpa only [at134, at111, Int.zero_add] using certified
theorem check465 (p : Pattern) : (!walkGuard soko2_2.board support p 134 111 .northWest || decide (bonus 134 p ≤ bonus 111 p)) = true :=
  check_of_implication _ _ (bound465 p)
theorem guard466 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 157 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound466 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 157 .southEast = true) : bonus 134 p ≤ bonus 157 p := by
  have certified := compare0 p (guard466 p guard)
  simpa only [at134, at157, Int.zero_add] using certified
theorem check466 (p : Pattern) : (!walkGuard soko2_2.board support p 134 157 .southEast || decide (bonus 134 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound466 p)
theorem guard467 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 155 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound467 (p : Pattern) (guard : walkGuard soko2_2.board support p 134 155 .southWest = true) : bonus 134 p ≤ bonus 155 p := by
  have certified := compare0 p (guard467 p guard)
  simpa only [at134, at155, Int.zero_add] using certified
theorem check467 (p : Pattern) : (!walkGuard soko2_2.board support p 134 155 .southWest || decide (bonus 134 p ≤ bonus 155 p)) = true :=
  check_of_implication _ _ (bound467 p)
theorem guard468 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 113 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound468 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 113 .north = true) : bonus 135 p ≤ bonus 113 p := by
  have certified := compare0 p (guard468 p guard)
  simpa only [at135, at113, Int.zero_add] using certified
theorem check468 (p : Pattern) : (!walkGuard soko2_2.board support p 135 113 .north || decide (bonus 135 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound468 p)
theorem guard469 (p : Pattern) (guard : pushGuard support p 135 113 91 91 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound469 (p : Pattern) (guard : pushGuard support p 135 113 91 91 = true) : bonus 135 p ≤ 1 + Generated.soko2_2Potential.boulder 91 - Generated.soko2_2Potential.boulder 113 + bonus 113 (change p 113 (some 91)) := by
  have certified := compare2458 p (guard469 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 113 (some 91))
  have normalized := agree267 _ _ (change_representative support p 113 (some 91) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check469 (p : Pattern) : (!pushGuard support p 135 113 91 91 || decide (bonus 135 p ≤ 1 + Generated.soko2_2Potential.boulder 91 - Generated.soko2_2Potential.boulder 113 + bonus 113 (change p 113 (some 91)))) = true :=
  check_of_implication _ _ (bound469 p)
theorem guard470 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 157 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound470 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 157 .south = true) : bonus 135 p ≤ bonus 157 p := by
  have certified := compare0 p (guard470 p guard)
  simpa only [at135, at157, Int.zero_add] using certified
theorem check470 (p : Pattern) : (!walkGuard soko2_2.board support p 135 157 .south || decide (bonus 135 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound470 p)
theorem guard471 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 136 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound471 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 136 .east = true) : bonus 135 p ≤ bonus 136 p := by
  have certified := compare0 p (guard471 p guard)
  simpa only [at135, at136, Int.zero_add] using certified
theorem check471 (p : Pattern) : (!walkGuard soko2_2.board support p 135 136 .east || decide (bonus 135 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound471 p)
theorem guard472 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 134 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound472 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 134 .west = true) : bonus 135 p ≤ bonus 134 p := by
  have certified := compare0 p (guard472 p guard)
  simpa only [at135, at134, Int.zero_add] using certified
theorem check472 (p : Pattern) : (!walkGuard soko2_2.board support p 135 134 .west || decide (bonus 135 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound472 p)
theorem guard473 (p : Pattern) (guard : pushGuard support p 135 134 133 133 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound473 (p : Pattern) (guard : pushGuard support p 135 134 133 133 = true) : bonus 135 p ≤ 1 + Generated.soko2_2Potential.boulder 133 - Generated.soko2_2Potential.boulder 134 + bonus 134 (change p 134 (some 133)) := by
  have certified := compare2458 p (guard473 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 134 (some 133))
  have normalized := agree267 _ _ (change_representative support p 134 (some 133) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check473 (p : Pattern) : (!pushGuard support p 135 134 133 133 || decide (bonus 135 p ≤ 1 + Generated.soko2_2Potential.boulder 133 - Generated.soko2_2Potential.boulder 134 + bonus 134 (change p 134 (some 133)))) = true :=
  check_of_implication _ _ (bound473 p)
theorem guard474 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 114 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound474 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 114 .northEast = true) : bonus 135 p ≤ bonus 114 p := by
  have certified := compare0 p (guard474 p guard)
  simpa only [at135, at114, Int.zero_add] using certified
theorem check474 (p : Pattern) : (!walkGuard soko2_2.board support p 135 114 .northEast || decide (bonus 135 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound474 p)
theorem guard475 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 158 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound475 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 158 .southEast = true) : bonus 135 p ≤ bonus 158 p := by
  have certified := compare0 p (guard475 p guard)
  simpa only [at135, at158, Int.zero_add] using certified
theorem check475 (p : Pattern) : (!walkGuard soko2_2.board support p 135 158 .southEast || decide (bonus 135 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound475 p)
theorem guard476 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 156 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound476 (p : Pattern) (guard : walkGuard soko2_2.board support p 135 156 .southWest = true) : bonus 135 p ≤ bonus 156 p := by
  have certified := compare0 p (guard476 p guard)
  simpa only [at135, at156, Int.zero_add] using certified
theorem check476 (p : Pattern) : (!walkGuard soko2_2.board support p 135 156 .southWest || decide (bonus 135 p ≤ bonus 156 p)) = true :=
  check_of_implication _ _ (bound476 p)
theorem guard477 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 114 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound477 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 114 .north = true) : bonus 136 p ≤ bonus 114 p := by
  have certified := compare0 p (guard477 p guard)
  simpa only [at136, at114, Int.zero_add] using certified
theorem check477 (p : Pattern) : (!walkGuard soko2_2.board support p 136 114 .north || decide (bonus 136 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound477 p)
theorem guard478 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 158 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound478 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 158 .south = true) : bonus 136 p ≤ bonus 158 p := by
  have certified := compare0 p (guard478 p guard)
  simpa only [at136, at158, Int.zero_add] using certified
theorem check478 (p : Pattern) : (!walkGuard soko2_2.board support p 136 158 .south || decide (bonus 136 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound478 p)
theorem guard479 (p : Pattern) (guard : pushGuard support p 136 158 180 180 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound479 (p : Pattern) (guard : pushGuard support p 136 158 180 180 = true) : bonus 136 p ≤ 1 + Generated.soko2_2Potential.boulder 180 - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some 180)) := by
  have certified := compare0 p (guard479 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 158 (some 180))
  have normalized := agree267 _ _ (change_representative support p 158 (some 180) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check479 (p : Pattern) : (!pushGuard support p 136 158 180 180 || decide (bonus 136 p ≤ 1 + Generated.soko2_2Potential.boulder 180 - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some 180)))) = true :=
  check_of_implication _ _ (bound479 p)
end NetHack.Sokoban22Refined85
