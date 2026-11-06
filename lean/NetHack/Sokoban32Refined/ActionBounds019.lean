import NetHack.Sokoban32Refined.ActionBounds018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard456 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 150 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound456 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 150 .southWest = true) : bonus 125 p ≤ bonus 150 p := by
  have certified := compare103 p (guard456 p guard)
  simpa only [at125, at150, Int.zero_add] using certified
theorem check456 (p : Pattern) : (!walkGuard soko3_2.board support p 125 150 .southWest || decide (bonus 125 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound456 p)
theorem guard457 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 100 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound457 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 100 .north = true) : bonus 126 p ≤ bonus 100 p := by
  have certified := compare103 p (guard457 p guard)
  simpa only [at126, at100, Int.zero_add] using certified
theorem check457 (p : Pattern) : (!walkGuard soko3_2.board support p 126 100 .north || decide (bonus 126 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound457 p)
theorem guard458 (p : Pattern) (guard : pushGuard support p 126 100 74 74 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound458 (p : Pattern) (guard : pushGuard support p 126 100 74 74 = true) : bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some 74)) := by
  have certified := compare37 p (guard458 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 100 (some 74))
  have normalized := agree0 _ _ (change_representative support p 100 (some 74) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check458 (p : Pattern) : (!pushGuard support p 126 100 74 74 || decide (bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some 74)))) = true :=
  check_of_implication _ _ (bound458 p)
theorem guard459 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 152 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound459 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 152 .south = true) : bonus 126 p ≤ bonus 152 p := by
  have certified := compare103 p (guard459 p guard)
  simpa only [at126, at152, Int.zero_add] using certified
theorem check459 (p : Pattern) : (!walkGuard soko3_2.board support p 126 152 .south || decide (bonus 126 p ≤ bonus 152 p)) = true :=
  check_of_implication _ _ (bound459 p)
theorem guard460 (p : Pattern) (guard : pushGuard support p 126 152 178 178 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound460 (p : Pattern) (guard : pushGuard support p 126 152 178 178 = true) : bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some 178)) := by
  have certified := compare37 p (guard460 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 152 (some 178))
  have normalized := agree0 _ _ (change_representative support p 152 (some 178) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check460 (p : Pattern) : (!pushGuard support p 126 152 178 178 || decide (bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some 178)))) = true :=
  check_of_implication _ _ (bound460 p)
theorem guard461 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 127 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound461 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 127 .east = true) : bonus 126 p ≤ bonus 127 p := by
  have certified := compare103 p (guard461 p guard)
  simpa only [at126, at127, Int.zero_add] using certified
theorem check461 (p : Pattern) : (!walkGuard soko3_2.board support p 126 127 .east || decide (bonus 126 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound461 p)
theorem guard462 (p : Pattern) (guard : pushGuard support p 126 127 128 128 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound462 (p : Pattern) (guard : pushGuard support p 126 127 128 128 = true) : bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder 128 - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some 128)) := by
  have certified := compare37 p (guard462 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 127 (some 128))
  have normalized := agree0 _ _ (change_representative support p 127 (some 128) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check462 (p : Pattern) : (!pushGuard support p 126 127 128 128 || decide (bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder 128 - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some 128)))) = true :=
  check_of_implication _ _ (bound462 p)
theorem guard463 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 125 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound463 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 125 .west = true) : bonus 126 p ≤ bonus 125 p := by
  have certified := compare103 p (guard463 p guard)
  simpa only [at126, at125, Int.zero_add] using certified
theorem check463 (p : Pattern) : (!walkGuard soko3_2.board support p 126 125 .west || decide (bonus 126 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound463 p)
theorem guard464 (p : Pattern) (guard : pushGuard support p 126 125 124 124 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound464 (p : Pattern) (guard : pushGuard support p 126 125 124 124 = true) : bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some 124)) := by
  have certified := compare37 p (guard464 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 125 (some 124))
  have normalized := agree0 _ _ (change_representative support p 125 (some 124) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check464 (p : Pattern) : (!pushGuard support p 126 125 124 124 || decide (bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some 124)))) = true :=
  check_of_implication _ _ (bound464 p)
theorem guard465 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 101 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound465 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 101 .northEast = true) : bonus 126 p ≤ bonus 101 p := by
  have certified := compare103 p (guard465 p guard)
  simpa only [at126, at101, Int.zero_add] using certified
theorem check465 (p : Pattern) : (!walkGuard soko3_2.board support p 126 101 .northEast || decide (bonus 126 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound465 p)
theorem guard466 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 99 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound466 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 99 .northWest = true) : bonus 126 p ≤ bonus 99 p := by
  have certified := compare103 p (guard466 p guard)
  simpa only [at126, at99, Int.zero_add] using certified
theorem check466 (p : Pattern) : (!walkGuard soko3_2.board support p 126 99 .northWest || decide (bonus 126 p ≤ bonus 99 p)) = true :=
  check_of_implication _ _ (bound466 p)
theorem guard467 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 153 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound467 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 153 .southEast = true) : bonus 126 p ≤ bonus 153 p := by
  have certified := compare103 p (guard467 p guard)
  simpa only [at126, at153, Int.zero_add] using certified
theorem check467 (p : Pattern) : (!walkGuard soko3_2.board support p 126 153 .southEast || decide (bonus 126 p ≤ bonus 153 p)) = true :=
  check_of_implication _ _ (bound467 p)
theorem guard468 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 151 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound468 (p : Pattern) (guard : walkGuard soko3_2.board support p 126 151 .southWest = true) : bonus 126 p ≤ bonus 151 p := by
  have certified := compare103 p (guard468 p guard)
  simpa only [at126, at151, Int.zero_add] using certified
theorem check468 (p : Pattern) : (!walkGuard soko3_2.board support p 126 151 .southWest || decide (bonus 126 p ≤ bonus 151 p)) = true :=
  check_of_implication _ _ (bound468 p)
theorem guard469 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 101 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound469 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 101 .north = true) : bonus 127 p ≤ bonus 101 p := by
  have certified := compare103 p (guard469 p guard)
  simpa only [at127, at101, Int.zero_add] using certified
theorem check469 (p : Pattern) : (!walkGuard soko3_2.board support p 127 101 .north || decide (bonus 127 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound469 p)
theorem guard470 (p : Pattern) (guard : pushGuard support p 127 101 75 75 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound470 (p : Pattern) (guard : pushGuard support p 127 101 75 75 = true) : bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder 75 - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some 75)) := by
  have certified := compare37 p (guard470 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 101 (some 75))
  have normalized := agree0 _ _ (change_representative support p 101 (some 75) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check470 (p : Pattern) : (!pushGuard support p 127 101 75 75 || decide (bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder 75 - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some 75)))) = true :=
  check_of_implication _ _ (bound470 p)
theorem guard471 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 153 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound471 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 153 .south = true) : bonus 127 p ≤ bonus 153 p := by
  have certified := compare103 p (guard471 p guard)
  simpa only [at127, at153, Int.zero_add] using certified
theorem check471 (p : Pattern) : (!walkGuard soko3_2.board support p 127 153 .south || decide (bonus 127 p ≤ bonus 153 p)) = true :=
  check_of_implication _ _ (bound471 p)
theorem guard472 (p : Pattern) (guard : pushGuard support p 127 153 179 179 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound472 (p : Pattern) (guard : pushGuard support p 127 153 179 179 = true) : bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some 179)) := by
  have certified := compare37 p (guard472 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 153 (some 179))
  have normalized := agree0 _ _ (change_representative support p 153 (some 179) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check472 (p : Pattern) : (!pushGuard support p 127 153 179 179 || decide (bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some 179)))) = true :=
  check_of_implication _ _ (bound472 p)
theorem guard473 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 128 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound473 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 128 .east = true) : bonus 127 p ≤ bonus 128 p := by
  have certified := compare103 p (guard473 p guard)
  simpa only [at127, at128, Int.zero_add] using certified
theorem check473 (p : Pattern) : (!walkGuard soko3_2.board support p 127 128 .east || decide (bonus 127 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound473 p)
theorem guard474 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 126 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound474 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 126 .west = true) : bonus 127 p ≤ bonus 126 p := by
  have certified := compare103 p (guard474 p guard)
  simpa only [at127, at126, Int.zero_add] using certified
theorem check474 (p : Pattern) : (!walkGuard soko3_2.board support p 127 126 .west || decide (bonus 127 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound474 p)
theorem guard475 (p : Pattern) (guard : pushGuard support p 127 126 125 125 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound475 (p : Pattern) (guard : pushGuard support p 127 126 125 125 = true) : bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some 125)) := by
  have certified := compare37 p (guard475 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 126 (some 125))
  have normalized := agree0 _ _ (change_representative support p 126 (some 125) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check475 (p : Pattern) : (!pushGuard support p 127 126 125 125 || decide (bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some 125)))) = true :=
  check_of_implication _ _ (bound475 p)
theorem guard476 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 102 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound476 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 102 .northEast = true) : bonus 127 p ≤ bonus 102 p := by
  have certified := compare103 p (guard476 p guard)
  simpa only [at127, at102, Int.zero_add] using certified
theorem check476 (p : Pattern) : (!walkGuard soko3_2.board support p 127 102 .northEast || decide (bonus 127 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound476 p)
theorem guard477 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 100 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound477 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 100 .northWest = true) : bonus 127 p ≤ bonus 100 p := by
  have certified := compare103 p (guard477 p guard)
  simpa only [at127, at100, Int.zero_add] using certified
theorem check477 (p : Pattern) : (!walkGuard soko3_2.board support p 127 100 .northWest || decide (bonus 127 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound477 p)
theorem guard478 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 154 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound478 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 154 .southEast = true) : bonus 127 p ≤ bonus 154 p := by
  have certified := compare103 p (guard478 p guard)
  simpa only [at127, at154, Int.zero_add] using certified
theorem check478 (p : Pattern) : (!walkGuard soko3_2.board support p 127 154 .southEast || decide (bonus 127 p ≤ bonus 154 p)) = true :=
  check_of_implication _ _ (bound478 p)
theorem guard479 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 152 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound479 (p : Pattern) (guard : walkGuard soko3_2.board support p 127 152 .southWest = true) : bonus 127 p ≤ bonus 152 p := by
  have certified := compare103 p (guard479 p guard)
  simpa only [at127, at152, Int.zero_add] using certified
theorem check479 (p : Pattern) : (!walkGuard soko3_2.board support p 127 152 .southWest || decide (bonus 127 p ≤ bonus 152 p)) = true :=
  check_of_implication _ _ (bound479 p)
end NetHack.Sokoban32Refined
