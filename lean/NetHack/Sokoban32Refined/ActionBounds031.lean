import NetHack.Sokoban32Refined.ActionBounds030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard744 (p : Pattern) (guard : pushGuard support p 173 174 175 175 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound744 (p : Pattern) (guard : pushGuard support p 173 174 175 175 = true) : bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some 175)) := by
  have certified := compare37 p (guard744 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 174 (some 175))
  have normalized := agree0 _ _ (change_representative support p 174 (some 175) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check744 (p : Pattern) : (!pushGuard support p 173 174 175 175 || decide (bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some 175)))) = true :=
  check_of_implication _ _ (bound744 p)
theorem guard745 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 172 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound745 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 172 .west = true) : bonus 173 p ≤ bonus 172 p := by
  have certified := compare103 p (guard745 p guard)
  simpa only [at173, at172, Int.zero_add] using certified
theorem check745 (p : Pattern) : (!walkGuard soko3_2.board support p 173 172 .west || decide (bonus 173 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound745 p)
theorem guard746 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 148 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound746 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 148 .northEast = true) : bonus 173 p ≤ bonus 148 p := by
  have certified := compare103 p (guard746 p guard)
  simpa only [at173, at148, Int.zero_add] using certified
theorem check746 (p : Pattern) : (!walkGuard soko3_2.board support p 173 148 .northEast || decide (bonus 173 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound746 p)
theorem guard747 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 146 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound747 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 146 .northWest = true) : bonus 173 p ≤ bonus 146 p := by
  have certified := compare103 p (guard747 p guard)
  simpa only [at173, at146, Int.zero_add] using certified
theorem check747 (p : Pattern) : (!walkGuard soko3_2.board support p 173 146 .northWest || decide (bonus 173 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound747 p)
theorem guard748 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 200 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound748 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 200 .southEast = true) : bonus 173 p ≤ bonus 200 p := by
  have certified := compare103 p (guard748 p guard)
  simpa only [at173, at200, Int.zero_add] using certified
theorem check748 (p : Pattern) : (!walkGuard soko3_2.board support p 173 200 .southEast || decide (bonus 173 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound748 p)
theorem guard749 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 198 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound749 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 198 .southWest = true) : bonus 173 p ≤ bonus 198 p := by
  have certified := compare103 p (guard749 p guard)
  simpa only [at173, at198, Int.zero_add] using certified
theorem check749 (p : Pattern) : (!walkGuard soko3_2.board support p 173 198 .southWest || decide (bonus 173 p ≤ bonus 198 p)) = true :=
  check_of_implication _ _ (bound749 p)
theorem guard750 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 148 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound750 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 148 .north = true) : bonus 174 p ≤ bonus 148 p := by
  have certified := compare103 p (guard750 p guard)
  simpa only [at174, at148, Int.zero_add] using certified
theorem check750 (p : Pattern) : (!walkGuard soko3_2.board support p 174 148 .north || decide (bonus 174 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound750 p)
theorem guard751 (p : Pattern) (guard : pushGuard support p 174 148 122 122 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound751 (p : Pattern) (guard : pushGuard support p 174 148 122 122 = true) : bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some 122)) := by
  have certified := compare37 p (guard751 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 148 (some 122))
  have normalized := agree0 _ _ (change_representative support p 148 (some 122) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check751 (p : Pattern) : (!pushGuard support p 174 148 122 122 || decide (bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some 122)))) = true :=
  check_of_implication _ _ (bound751 p)
theorem guard752 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 200 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound752 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 200 .south = true) : bonus 174 p ≤ bonus 200 p := by
  have certified := compare103 p (guard752 p guard)
  simpa only [at174, at200, Int.zero_add] using certified
theorem check752 (p : Pattern) : (!walkGuard soko3_2.board support p 174 200 .south || decide (bonus 174 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound752 p)
theorem guard753 (p : Pattern) (guard : pushGuard support p 174 200 226 226 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound753 (p : Pattern) (guard : pushGuard support p 174 200 226 226 = true) : bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder 226 - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some 226)) := by
  have certified := compare37 p (guard753 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 200 (some 226))
  have normalized := agree0 _ _ (change_representative support p 200 (some 226) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check753 (p : Pattern) : (!pushGuard support p 174 200 226 226 || decide (bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder 226 - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some 226)))) = true :=
  check_of_implication _ _ (bound753 p)
theorem guard754 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 175 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound754 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 175 .east = true) : bonus 174 p ≤ bonus 175 p := by
  have certified := compare103 p (guard754 p guard)
  simpa only [at174, at175, Int.zero_add] using certified
theorem check754 (p : Pattern) : (!walkGuard soko3_2.board support p 174 175 .east || decide (bonus 174 p ≤ bonus 175 p)) = true :=
  check_of_implication _ _ (bound754 p)
theorem guard755 (p : Pattern) (guard : pushGuard support p 174 175 176 176 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound755 (p : Pattern) (guard : pushGuard support p 174 175 176 176 = true) : bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some 176)) := by
  have certified := compare37 p (guard755 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 175 (some 176))
  have normalized := agree0 _ _ (change_representative support p 175 (some 176) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check755 (p : Pattern) : (!pushGuard support p 174 175 176 176 || decide (bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some 176)))) = true :=
  check_of_implication _ _ (bound755 p)
theorem guard756 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 173 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound756 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 173 .west = true) : bonus 174 p ≤ bonus 173 p := by
  have certified := compare103 p (guard756 p guard)
  simpa only [at174, at173, Int.zero_add] using certified
theorem check756 (p : Pattern) : (!walkGuard soko3_2.board support p 174 173 .west || decide (bonus 174 p ≤ bonus 173 p)) = true :=
  check_of_implication _ _ (bound756 p)
theorem guard757 (p : Pattern) (guard : pushGuard support p 174 173 172 172 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound757 (p : Pattern) (guard : pushGuard support p 174 173 172 172 = true) : bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder 172 - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some 172)) := by
  have certified := compare37 p (guard757 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 173 (some 172))
  have normalized := agree0 _ _ (change_representative support p 173 (some 172) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check757 (p : Pattern) : (!pushGuard support p 174 173 172 172 || decide (bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder 172 - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some 172)))) = true :=
  check_of_implication _ _ (bound757 p)
theorem guard758 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 149 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound758 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 149 .northEast = true) : bonus 174 p ≤ bonus 149 p := by
  have certified := compare103 p (guard758 p guard)
  simpa only [at174, at149, Int.zero_add] using certified
theorem check758 (p : Pattern) : (!walkGuard soko3_2.board support p 174 149 .northEast || decide (bonus 174 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound758 p)
theorem guard759 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 147 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound759 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 147 .northWest = true) : bonus 174 p ≤ bonus 147 p := by
  have certified := compare103 p (guard759 p guard)
  simpa only [at174, at147, Int.zero_add] using certified
theorem check759 (p : Pattern) : (!walkGuard soko3_2.board support p 174 147 .northWest || decide (bonus 174 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound759 p)
theorem guard760 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 201 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound760 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 201 .southEast = true) : bonus 174 p ≤ bonus 201 p := by
  have certified := compare103 p (guard760 p guard)
  simpa only [at174, at201, Int.zero_add] using certified
theorem check760 (p : Pattern) : (!walkGuard soko3_2.board support p 174 201 .southEast || decide (bonus 174 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound760 p)
theorem guard761 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 199 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound761 (p : Pattern) (guard : walkGuard soko3_2.board support p 174 199 .southWest = true) : bonus 174 p ≤ bonus 199 p := by
  have certified := compare103 p (guard761 p guard)
  simpa only [at174, at199, Int.zero_add] using certified
theorem check761 (p : Pattern) : (!walkGuard soko3_2.board support p 174 199 .southWest || decide (bonus 174 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound761 p)
theorem guard762 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 149 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound762 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 149 .north = true) : bonus 175 p ≤ bonus 149 p := by
  have certified := compare103 p (guard762 p guard)
  simpa only [at175, at149, Int.zero_add] using certified
theorem check762 (p : Pattern) : (!walkGuard soko3_2.board support p 175 149 .north || decide (bonus 175 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound762 p)
theorem guard763 (p : Pattern) (guard : pushGuard support p 175 149 123 123 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound763 (p : Pattern) (guard : pushGuard support p 175 149 123 123 = true) : bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some 123)) := by
  have certified := compare37 p (guard763 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 149 (some 123))
  have normalized := agree0 _ _ (change_representative support p 149 (some 123) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check763 (p : Pattern) : (!pushGuard support p 175 149 123 123 || decide (bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some 123)))) = true :=
  check_of_implication _ _ (bound763 p)
theorem guard764 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 201 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound764 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 201 .south = true) : bonus 175 p ≤ bonus 201 p := by
  have certified := compare103 p (guard764 p guard)
  simpa only [at175, at201, Int.zero_add] using certified
theorem check764 (p : Pattern) : (!walkGuard soko3_2.board support p 175 201 .south || decide (bonus 175 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound764 p)
theorem guard765 (p : Pattern) (guard : pushGuard support p 175 201 227 227 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound765 (p : Pattern) (guard : pushGuard support p 175 201 227 227 = true) : bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder 227 - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some 227)) := by
  have certified := compare37 p (guard765 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 201 (some 227))
  have normalized := agree0 _ _ (change_representative support p 201 (some 227) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check765 (p : Pattern) : (!pushGuard support p 175 201 227 227 || decide (bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder 227 - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some 227)))) = true :=
  check_of_implication _ _ (bound765 p)
theorem guard766 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 176 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound766 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 176 .east = true) : bonus 175 p ≤ bonus 176 p := by
  have certified := compare103 p (guard766 p guard)
  simpa only [at175, at176, Int.zero_add] using certified
theorem check766 (p : Pattern) : (!walkGuard soko3_2.board support p 175 176 .east || decide (bonus 175 p ≤ bonus 176 p)) = true :=
  check_of_implication _ _ (bound766 p)
theorem guard767 (p : Pattern) (guard : pushGuard support p 175 176 177 177 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound767 (p : Pattern) (guard : pushGuard support p 175 176 177 177 = true) : bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some 177)) := by
  have certified := compare37 p (guard767 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 176 (some 177))
  have normalized := agree0 _ _ (change_representative support p 176 (some 177) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check767 (p : Pattern) : (!pushGuard support p 175 176 177 177 || decide (bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some 177)))) = true :=
  check_of_implication _ _ (bound767 p)
end NetHack.Sokoban32Refined
