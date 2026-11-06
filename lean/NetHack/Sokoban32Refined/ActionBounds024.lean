import NetHack.Sokoban32Refined.ActionBounds023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard576 (p : Pattern) (guard : pushGuard support p 147 121 95 95 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound576 (p : Pattern) (guard : pushGuard support p 147 121 95 95 = true) : bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some 95)) := by
  have certified := compare37 p (guard576 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 121 (some 95))
  have normalized := agree0 _ _ (change_representative support p 121 (some 95) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check576 (p : Pattern) : (!pushGuard support p 147 121 95 95 || decide (bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some 95)))) = true :=
  check_of_implication _ _ (bound576 p)
theorem guard577 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 173 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound577 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 173 .south = true) : bonus 147 p ≤ bonus 173 p := by
  have certified := compare103 p (guard577 p guard)
  simpa only [at147, at173, Int.zero_add] using certified
theorem check577 (p : Pattern) : (!walkGuard soko3_2.board support p 147 173 .south || decide (bonus 147 p ≤ bonus 173 p)) = true :=
  check_of_implication _ _ (bound577 p)
theorem guard578 (p : Pattern) (guard : pushGuard support p 147 173 199 199 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound578 (p : Pattern) (guard : pushGuard support p 147 173 199 199 = true) : bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder 199 - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some 199)) := by
  have certified := compare37 p (guard578 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 173 (some 199))
  have normalized := agree0 _ _ (change_representative support p 173 (some 199) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check578 (p : Pattern) : (!pushGuard support p 147 173 199 199 || decide (bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder 199 - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some 199)))) = true :=
  check_of_implication _ _ (bound578 p)
theorem guard579 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 148 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound579 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 148 .east = true) : bonus 147 p ≤ bonus 148 p := by
  have certified := compare103 p (guard579 p guard)
  simpa only [at147, at148, Int.zero_add] using certified
theorem check579 (p : Pattern) : (!walkGuard soko3_2.board support p 147 148 .east || decide (bonus 147 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound579 p)
theorem guard580 (p : Pattern) (guard : pushGuard support p 147 148 149 149 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound580 (p : Pattern) (guard : pushGuard support p 147 148 149 149 = true) : bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some 149)) := by
  have certified := compare37 p (guard580 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 148 (some 149))
  have normalized := agree0 _ _ (change_representative support p 148 (some 149) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check580 (p : Pattern) : (!pushGuard support p 147 148 149 149 || decide (bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some 149)))) = true :=
  check_of_implication _ _ (bound580 p)
theorem guard581 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 146 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound581 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 146 .west = true) : bonus 147 p ≤ bonus 146 p := by
  have certified := compare103 p (guard581 p guard)
  simpa only [at147, at146, Int.zero_add] using certified
theorem check581 (p : Pattern) : (!walkGuard soko3_2.board support p 147 146 .west || decide (bonus 147 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound581 p)
theorem guard582 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 122 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound582 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 122 .northEast = true) : bonus 147 p ≤ bonus 122 p := by
  have certified := compare103 p (guard582 p guard)
  simpa only [at147, at122, Int.zero_add] using certified
theorem check582 (p : Pattern) : (!walkGuard soko3_2.board support p 147 122 .northEast || decide (bonus 147 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound582 p)
theorem guard583 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 120 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound583 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 120 .northWest = true) : bonus 147 p ≤ bonus 120 p := by
  have certified := compare103 p (guard583 p guard)
  simpa only [at147, at120, Int.zero_add] using certified
theorem check583 (p : Pattern) : (!walkGuard soko3_2.board support p 147 120 .northWest || decide (bonus 147 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound583 p)
theorem guard584 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 174 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound584 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 174 .southEast = true) : bonus 147 p ≤ bonus 174 p := by
  have certified := compare103 p (guard584 p guard)
  simpa only [at147, at174, Int.zero_add] using certified
theorem check584 (p : Pattern) : (!walkGuard soko3_2.board support p 147 174 .southEast || decide (bonus 147 p ≤ bonus 174 p)) = true :=
  check_of_implication _ _ (bound584 p)
theorem guard585 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 172 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound585 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 172 .southWest = true) : bonus 147 p ≤ bonus 172 p := by
  have certified := compare103 p (guard585 p guard)
  simpa only [at147, at172, Int.zero_add] using certified
theorem check585 (p : Pattern) : (!walkGuard soko3_2.board support p 147 172 .southWest || decide (bonus 147 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound585 p)
theorem guard586 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 122 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound586 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 122 .north = true) : bonus 148 p ≤ bonus 122 p := by
  have certified := compare103 p (guard586 p guard)
  simpa only [at148, at122, Int.zero_add] using certified
theorem check586 (p : Pattern) : (!walkGuard soko3_2.board support p 148 122 .north || decide (bonus 148 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound586 p)
theorem guard587 (p : Pattern) (guard : pushGuard support p 148 122 96 96 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound587 (p : Pattern) (guard : pushGuard support p 148 122 96 96 = true) : bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some 96)) := by
  have certified := compare37 p (guard587 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 122 (some 96))
  have normalized := agree0 _ _ (change_representative support p 122 (some 96) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check587 (p : Pattern) : (!pushGuard support p 148 122 96 96 || decide (bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some 96)))) = true :=
  check_of_implication _ _ (bound587 p)
theorem guard588 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 174 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound588 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 174 .south = true) : bonus 148 p ≤ bonus 174 p := by
  have certified := compare103 p (guard588 p guard)
  simpa only [at148, at174, Int.zero_add] using certified
theorem check588 (p : Pattern) : (!walkGuard soko3_2.board support p 148 174 .south || decide (bonus 148 p ≤ bonus 174 p)) = true :=
  check_of_implication _ _ (bound588 p)
theorem guard589 (p : Pattern) (guard : pushGuard support p 148 174 200 200 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound589 (p : Pattern) (guard : pushGuard support p 148 174 200 200 = true) : bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some 200)) := by
  have certified := compare37 p (guard589 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 174 (some 200))
  have normalized := agree0 _ _ (change_representative support p 174 (some 200) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check589 (p : Pattern) : (!pushGuard support p 148 174 200 200 || decide (bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some 200)))) = true :=
  check_of_implication _ _ (bound589 p)
theorem guard590 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 149 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound590 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 149 .east = true) : bonus 148 p ≤ bonus 149 p := by
  have certified := compare103 p (guard590 p guard)
  simpa only [at148, at149, Int.zero_add] using certified
theorem check590 (p : Pattern) : (!walkGuard soko3_2.board support p 148 149 .east || decide (bonus 148 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound590 p)
theorem guard591 (p : Pattern) (guard : pushGuard support p 148 149 150 150 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound591 (p : Pattern) (guard : pushGuard support p 148 149 150 150 = true) : bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some 150)) := by
  have certified := compare37 p (guard591 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 149 (some 150))
  have normalized := agree0 _ _ (change_representative support p 149 (some 150) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check591 (p : Pattern) : (!pushGuard support p 148 149 150 150 || decide (bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some 150)))) = true :=
  check_of_implication _ _ (bound591 p)
theorem guard592 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 147 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound592 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 147 .west = true) : bonus 148 p ≤ bonus 147 p := by
  have certified := compare103 p (guard592 p guard)
  simpa only [at148, at147, Int.zero_add] using certified
theorem check592 (p : Pattern) : (!walkGuard soko3_2.board support p 148 147 .west || decide (bonus 148 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound592 p)
theorem guard593 (p : Pattern) (guard : pushGuard support p 148 147 146 146 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound593 (p : Pattern) (guard : pushGuard support p 148 147 146 146 = true) : bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder 146 - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some 146)) := by
  have certified := compare37 p (guard593 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 147 (some 146))
  have normalized := agree0 _ _ (change_representative support p 147 (some 146) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check593 (p : Pattern) : (!pushGuard support p 148 147 146 146 || decide (bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder 146 - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some 146)))) = true :=
  check_of_implication _ _ (bound593 p)
theorem guard594 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 123 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound594 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 123 .northEast = true) : bonus 148 p ≤ bonus 123 p := by
  have certified := compare103 p (guard594 p guard)
  simpa only [at148, at123, Int.zero_add] using certified
theorem check594 (p : Pattern) : (!walkGuard soko3_2.board support p 148 123 .northEast || decide (bonus 148 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound594 p)
theorem guard595 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 121 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound595 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 121 .northWest = true) : bonus 148 p ≤ bonus 121 p := by
  have certified := compare103 p (guard595 p guard)
  simpa only [at148, at121, Int.zero_add] using certified
theorem check595 (p : Pattern) : (!walkGuard soko3_2.board support p 148 121 .northWest || decide (bonus 148 p ≤ bonus 121 p)) = true :=
  check_of_implication _ _ (bound595 p)
theorem guard596 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 175 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound596 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 175 .southEast = true) : bonus 148 p ≤ bonus 175 p := by
  have certified := compare103 p (guard596 p guard)
  simpa only [at148, at175, Int.zero_add] using certified
theorem check596 (p : Pattern) : (!walkGuard soko3_2.board support p 148 175 .southEast || decide (bonus 148 p ≤ bonus 175 p)) = true :=
  check_of_implication _ _ (bound596 p)
theorem guard597 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 173 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound597 (p : Pattern) (guard : walkGuard soko3_2.board support p 148 173 .southWest = true) : bonus 148 p ≤ bonus 173 p := by
  have certified := compare103 p (guard597 p guard)
  simpa only [at148, at173, Int.zero_add] using certified
theorem check597 (p : Pattern) : (!walkGuard soko3_2.board support p 148 173 .southWest || decide (bonus 148 p ≤ bonus 173 p)) = true :=
  check_of_implication _ _ (bound597 p)
theorem guard598 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 123 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound598 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 123 .north = true) : bonus 149 p ≤ bonus 123 p := by
  have certified := compare103 p (guard598 p guard)
  simpa only [at149, at123, Int.zero_add] using certified
theorem check598 (p : Pattern) : (!walkGuard soko3_2.board support p 149 123 .north || decide (bonus 149 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound598 p)
theorem guard599 (p : Pattern) (guard : pushGuard support p 149 123 97 97 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound599 (p : Pattern) (guard : pushGuard support p 149 123 97 97 = true) : bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some 97)) := by
  have certified := compare37 p (guard599 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 123 (some 97))
  have normalized := agree0 _ _ (change_representative support p 123 (some 97) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check599 (p : Pattern) : (!pushGuard support p 149 123 97 97 || decide (bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some 97)))) = true :=
  check_of_implication _ _ (bound599 p)
end NetHack.Sokoban32Refined
