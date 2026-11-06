import NetHack.Sokoban22Refined85.ActionBounds023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard576 (p : Pattern) (guard : pushGuard support p 155 133 111 111 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound576 (p : Pattern) (guard : pushGuard support p 155 133 111 111 = true) : bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder 111 - Generated.soko2_2Potential.boulder 133 + bonus 133 (change p 133 (some 111)) := by
  have certified := compare1 p (guard576 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 133 (some 111))
  have normalized := agree267 _ _ (change_representative support p 133 (some 111) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check576 (p : Pattern) : (!pushGuard support p 155 133 111 111 || decide (bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder 111 - Generated.soko2_2Potential.boulder 133 + bonus 133 (change p 133 (some 111)))) = true :=
  check_of_implication _ _ (bound576 p)
theorem guard577 (p : Pattern) (guard : walkGuard soko2_2.board support p 155 177 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound577 (p : Pattern) (guard : walkGuard soko2_2.board support p 155 177 .south = true) : bonus 155 p ≤ bonus 177 p := by
  have certified := compare0 p (guard577 p guard)
  simpa only [at155, at177, Int.zero_add] using certified
theorem check577 (p : Pattern) : (!walkGuard soko2_2.board support p 155 177 .south || decide (bonus 155 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound577 p)
theorem guard578 (p : Pattern) (guard : pushGuard support p 155 177 199 199 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound578 (p : Pattern) (guard : pushGuard support p 155 177 199 199 = true) : bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder 199 - Generated.soko2_2Potential.boulder 177 + bonus 177 (change p 177 (some 199)) := by
  have certified := compare1 p (guard578 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 177 (some 199))
  have normalized := agree267 _ _ (change_representative support p 177 (some 199) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check578 (p : Pattern) : (!pushGuard support p 155 177 199 199 || decide (bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder 199 - Generated.soko2_2Potential.boulder 177 + bonus 177 (change p 177 (some 199)))) = true :=
  check_of_implication _ _ (bound578 p)
theorem guard579 (p : Pattern) (guard : walkGuard soko2_2.board support p 155 156 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound579 (p : Pattern) (guard : walkGuard soko2_2.board support p 155 156 .east = true) : bonus 155 p ≤ bonus 156 p := by
  have certified := compare0 p (guard579 p guard)
  simpa only [at155, at156, Int.zero_add] using certified
theorem check579 (p : Pattern) : (!walkGuard soko2_2.board support p 155 156 .east || decide (bonus 155 p ≤ bonus 156 p)) = true :=
  check_of_implication _ _ (bound579 p)
theorem guard580 (p : Pattern) (guard : pushGuard support p 155 156 157 157 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound580 (p : Pattern) (guard : pushGuard support p 155 156 157 157 = true) : bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder 157 - Generated.soko2_2Potential.boulder 156 + bonus 156 (change p 156 (some 157)) := by
  have certified := compare0 p (guard580 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 156 (some 157))
  have normalized := agree267 _ _ (change_representative support p 156 (some 157) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check580 (p : Pattern) : (!pushGuard support p 155 156 157 157 || decide (bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder 157 - Generated.soko2_2Potential.boulder 156 + bonus 156 (change p 156 (some 157)))) = true :=
  check_of_implication _ _ (bound580 p)
theorem guard581 (p : Pattern) (guard : walkGuard soko2_2.board support p 155 134 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound581 (p : Pattern) (guard : walkGuard soko2_2.board support p 155 134 .northEast = true) : bonus 155 p ≤ bonus 134 p := by
  have certified := compare0 p (guard581 p guard)
  simpa only [at155, at134, Int.zero_add] using certified
theorem check581 (p : Pattern) : (!walkGuard soko2_2.board support p 155 134 .northEast || decide (bonus 155 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound581 p)
theorem guard582 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 134 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound582 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 134 .north = true) : bonus 156 p ≤ bonus 134 p := by
  have certified := compare0 p (guard582 p guard)
  simpa only [at156, at134, Int.zero_add] using certified
theorem check582 (p : Pattern) : (!walkGuard soko2_2.board support p 156 134 .north || decide (bonus 156 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound582 p)
theorem guard583 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 157 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound583 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 157 .east = true) : bonus 156 p ≤ bonus 157 p := by
  have certified := compare0 p (guard583 p guard)
  simpa only [at156, at157, Int.zero_add] using certified
theorem check583 (p : Pattern) : (!walkGuard soko2_2.board support p 156 157 .east || decide (bonus 156 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound583 p)
theorem guard584 (p : Pattern) (guard : pushGuard support p 156 157 158 158 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound584 (p : Pattern) (guard : pushGuard support p 156 157 158 158 = true) : bonus 156 p ≤ 1 + Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.boulder 157 + bonus 157 (change p 157 (some 158)) := by
  have certified := compare0 p (guard584 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 157 (some 158))
  have normalized := agree267 _ _ (change_representative support p 157 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check584 (p : Pattern) : (!pushGuard support p 156 157 158 158 || decide (bonus 156 p ≤ 1 + Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.boulder 157 + bonus 157 (change p 157 (some 158)))) = true :=
  check_of_implication _ _ (bound584 p)
theorem guard585 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 155 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound585 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 155 .west = true) : bonus 156 p ≤ bonus 155 p := by
  have certified := compare0 p (guard585 p guard)
  simpa only [at156, at155, Int.zero_add] using certified
theorem check585 (p : Pattern) : (!walkGuard soko2_2.board support p 156 155 .west || decide (bonus 156 p ≤ bonus 155 p)) = true :=
  check_of_implication _ _ (bound585 p)
theorem guard586 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 135 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound586 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 135 .northEast = true) : bonus 156 p ≤ bonus 135 p := by
  have certified := compare0 p (guard586 p guard)
  simpa only [at156, at135, Int.zero_add] using certified
theorem check586 (p : Pattern) : (!walkGuard soko2_2.board support p 156 135 .northEast || decide (bonus 156 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound586 p)
theorem guard587 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 133 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound587 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 133 .northWest = true) : bonus 156 p ≤ bonus 133 p := by
  have certified := compare0 p (guard587 p guard)
  simpa only [at156, at133, Int.zero_add] using certified
theorem check587 (p : Pattern) : (!walkGuard soko2_2.board support p 156 133 .northWest || decide (bonus 156 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound587 p)
theorem guard588 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 177 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound588 (p : Pattern) (guard : walkGuard soko2_2.board support p 156 177 .southWest = true) : bonus 156 p ≤ bonus 177 p := by
  have certified := compare0 p (guard588 p guard)
  simpa only [at156, at177, Int.zero_add] using certified
theorem check588 (p : Pattern) : (!walkGuard soko2_2.board support p 156 177 .southWest || decide (bonus 156 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound588 p)
theorem guard589 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 135 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound589 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 135 .north = true) : bonus 157 p ≤ bonus 135 p := by
  have certified := compare0 p (guard589 p guard)
  simpa only [at157, at135, Int.zero_add] using certified
theorem check589 (p : Pattern) : (!walkGuard soko2_2.board support p 157 135 .north || decide (bonus 157 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound589 p)
theorem guard590 (p : Pattern) (guard : pushGuard support p 157 135 113 113 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound590 (p : Pattern) (guard : pushGuard support p 157 135 113 113 = true) : bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder 113 - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some 113)) := by
  have certified := compare2458 p (guard590 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 135 (some 113))
  have normalized := agree267 _ _ (change_representative support p 135 (some 113) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check590 (p : Pattern) : (!pushGuard support p 157 135 113 113 || decide (bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder 113 - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some 113)))) = true :=
  check_of_implication _ _ (bound590 p)
theorem guard591 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 158 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound591 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 158 .east = true) : bonus 157 p ≤ bonus 158 p := by
  have certified := compare0 p (guard591 p guard)
  simpa only [at157, at158, Int.zero_add] using certified
theorem check591 (p : Pattern) : (!walkGuard soko2_2.board support p 157 158 .east || decide (bonus 157 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound591 p)
theorem guard592 (p : Pattern) (guard : pushGuard support p 157 158 159 159 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound592 (p : Pattern) (guard : pushGuard support p 157 158 159 159 = true) : bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder 159 - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some 159)) := by
  have certified := compare0 p (guard592 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 158 (some 159))
  have normalized := agree267 _ _ (change_representative support p 158 (some 159) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check592 (p : Pattern) : (!pushGuard support p 157 158 159 159 || decide (bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder 159 - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some 159)))) = true :=
  check_of_implication _ _ (bound592 p)
theorem guard593 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 156 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound593 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 156 .west = true) : bonus 157 p ≤ bonus 156 p := by
  have certified := compare0 p (guard593 p guard)
  simpa only [at157, at156, Int.zero_add] using certified
theorem check593 (p : Pattern) : (!walkGuard soko2_2.board support p 157 156 .west || decide (bonus 157 p ≤ bonus 156 p)) = true :=
  check_of_implication _ _ (bound593 p)
theorem guard594 (p : Pattern) (guard : pushGuard support p 157 156 155 155 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound594 (p : Pattern) (guard : pushGuard support p 157 156 155 155 = true) : bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder 155 - Generated.soko2_2Potential.boulder 156 + bonus 156 (change p 156 (some 155)) := by
  have certified := compare4416 p (guard594 p guard)
  change d267 p ≤ (3 : Int) + d267 (change p 156 (some 155))
  have normalized := agree267 _ _ (change_representative support p 156 (some 155) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (3 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check594 (p : Pattern) : (!pushGuard support p 157 156 155 155 || decide (bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder 155 - Generated.soko2_2Potential.boulder 156 + bonus 156 (change p 156 (some 155)))) = true :=
  check_of_implication _ _ (bound594 p)
theorem guard595 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 136 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound595 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 136 .northEast = true) : bonus 157 p ≤ bonus 136 p := by
  have certified := compare0 p (guard595 p guard)
  simpa only [at157, at136, Int.zero_add] using certified
theorem check595 (p : Pattern) : (!walkGuard soko2_2.board support p 157 136 .northEast || decide (bonus 157 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound595 p)
theorem guard596 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 134 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound596 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 134 .northWest = true) : bonus 157 p ≤ bonus 134 p := by
  have certified := compare0 p (guard596 p guard)
  simpa only [at157, at134, Int.zero_add] using certified
theorem check596 (p : Pattern) : (!walkGuard soko2_2.board support p 157 134 .northWest || decide (bonus 157 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound596 p)
theorem guard597 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 180 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound597 (p : Pattern) (guard : walkGuard soko2_2.board support p 157 180 .southEast = true) : bonus 157 p ≤ bonus 180 p := by
  have certified := compare0 p (guard597 p guard)
  simpa only [at157, at180, Int.zero_add] using certified
theorem check597 (p : Pattern) : (!walkGuard soko2_2.board support p 157 180 .southEast || decide (bonus 157 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound597 p)
theorem guard598 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 136 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound598 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 136 .north = true) : bonus 158 p ≤ bonus 136 p := by
  have certified := compare0 p (guard598 p guard)
  simpa only [at158, at136, Int.zero_add] using certified
theorem check598 (p : Pattern) : (!walkGuard soko2_2.board support p 158 136 .north || decide (bonus 158 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound598 p)
theorem guard599 (p : Pattern) (guard : pushGuard support p 158 136 114 114 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound599 (p : Pattern) (guard : pushGuard support p 158 136 114 114 = true) : bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder 114 - Generated.soko2_2Potential.boulder 136 + bonus 136 (change p 136 (some 114)) := by
  have certified := compare2458 p (guard599 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 136 (some 114))
  have normalized := agree267 _ _ (change_representative support p 136 (some 114) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check599 (p : Pattern) : (!pushGuard support p 158 136 114 114 || decide (bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder 114 - Generated.soko2_2Potential.boulder 136 + bonus 136 (change p 136 (some 114)))) = true :=
  check_of_implication _ _ (bound599 p)
end NetHack.Sokoban22Refined85
