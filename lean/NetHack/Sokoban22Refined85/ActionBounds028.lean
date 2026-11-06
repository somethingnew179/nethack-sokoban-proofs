import NetHack.Sokoban22Refined85.ActionBounds027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard672 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 146 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound672 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 146 .north = true) : bonus 168 p ≤ bonus 146 p := by
  have certified := compare1086 p (guard672 p guard)
  simpa only [at168, at146, Int.zero_add] using certified
theorem check672 (p : Pattern) : (!walkGuard soko2_2.board support p 168 146 .north || decide (bonus 168 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound672 p)
theorem guard673 (p : Pattern) (guard : pushGuard support p 168 146 124 124 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound673 (p : Pattern) (guard : pushGuard support p 168 146 124 124 = true) : bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some 124)) := by
  have certified := compare1087 p (guard673 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 146 (some 124))
  have normalized := agree0 _ _ (change_representative support p 146 (some 124) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check673 (p : Pattern) : (!pushGuard support p 168 146 124 124 || decide (bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some 124)))) = true :=
  check_of_implication _ _ (bound673 p)
theorem guard674 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 190 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound674 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 190 .south = true) : bonus 168 p ≤ bonus 190 p := by
  have certified := compare1086 p (guard674 p guard)
  simpa only [at168, at190, Int.zero_add] using certified
theorem check674 (p : Pattern) : (!walkGuard soko2_2.board support p 168 190 .south || decide (bonus 168 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound674 p)
theorem guard675 (p : Pattern) (guard : pushGuard support p 168 190 212 212 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound675 (p : Pattern) (guard : pushGuard support p 168 190 212 212 = true) : bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder 212 - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some 212)) := by
  have certified := compare1087 p (guard675 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 190 (some 212))
  have normalized := agree0 _ _ (change_representative support p 190 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check675 (p : Pattern) : (!pushGuard support p 168 190 212 212 || decide (bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder 212 - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some 212)))) = true :=
  check_of_implication _ _ (bound675 p)
theorem guard676 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 169 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound676 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 169 .east = true) : bonus 168 p ≤ bonus 169 p := by
  have certified := compare1086 p (guard676 p guard)
  simpa only [at168, at169, Int.zero_add] using certified
theorem check676 (p : Pattern) : (!walkGuard soko2_2.board support p 168 169 .east || decide (bonus 168 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound676 p)
theorem guard677 (p : Pattern) (guard : pushGuard support p 168 169 170 170 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound677 (p : Pattern) (guard : pushGuard support p 168 169 170 170 = true) : bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some 170)) := by
  have certified := compare1087 p (guard677 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 169 (some 170))
  have normalized := agree0 _ _ (change_representative support p 169 (some 170) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check677 (p : Pattern) : (!pushGuard support p 168 169 170 170 || decide (bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some 170)))) = true :=
  check_of_implication _ _ (bound677 p)
theorem guard678 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 167 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound678 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 167 .west = true) : bonus 168 p ≤ bonus 167 p := by
  have certified := compare1086 p (guard678 p guard)
  simpa only [at168, at167, Int.zero_add] using certified
theorem check678 (p : Pattern) : (!walkGuard soko2_2.board support p 168 167 .west || decide (bonus 168 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound678 p)
theorem guard679 (p : Pattern) (guard : pushGuard support p 168 167 166 166 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound679 (p : Pattern) (guard : pushGuard support p 168 167 166 166 = true) : bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder 166 - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some 166)) := by
  have certified := compare1087 p (guard679 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 167 (some 166))
  have normalized := agree0 _ _ (change_representative support p 167 (some 166) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check679 (p : Pattern) : (!pushGuard support p 168 167 166 166 || decide (bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder 166 - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some 166)))) = true :=
  check_of_implication _ _ (bound679 p)
theorem guard680 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 147 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound680 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 147 .northEast = true) : bonus 168 p ≤ bonus 147 p := by
  have certified := compare1086 p (guard680 p guard)
  simpa only [at168, at147, Int.zero_add] using certified
theorem check680 (p : Pattern) : (!walkGuard soko2_2.board support p 168 147 .northEast || decide (bonus 168 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound680 p)
theorem guard681 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 145 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound681 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 145 .northWest = true) : bonus 168 p ≤ bonus 145 p := by
  have certified := compare1086 p (guard681 p guard)
  simpa only [at168, at145, Int.zero_add] using certified
theorem check681 (p : Pattern) : (!walkGuard soko2_2.board support p 168 145 .northWest || decide (bonus 168 p ≤ bonus 145 p)) = true :=
  check_of_implication _ _ (bound681 p)
theorem guard682 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 191 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound682 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 191 .southEast = true) : bonus 168 p ≤ bonus 191 p := by
  have certified := compare1086 p (guard682 p guard)
  simpa only [at168, at191, Int.zero_add] using certified
theorem check682 (p : Pattern) : (!walkGuard soko2_2.board support p 168 191 .southEast || decide (bonus 168 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound682 p)
theorem guard683 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 189 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound683 (p : Pattern) (guard : walkGuard soko2_2.board support p 168 189 .southWest = true) : bonus 168 p ≤ bonus 189 p := by
  have certified := compare1086 p (guard683 p guard)
  simpa only [at168, at189, Int.zero_add] using certified
theorem check683 (p : Pattern) : (!walkGuard soko2_2.board support p 168 189 .southWest || decide (bonus 168 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound683 p)
theorem guard684 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 147 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound684 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 147 .north = true) : bonus 169 p ≤ bonus 147 p := by
  have certified := compare1086 p (guard684 p guard)
  simpa only [at169, at147, Int.zero_add] using certified
theorem check684 (p : Pattern) : (!walkGuard soko2_2.board support p 169 147 .north || decide (bonus 169 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound684 p)
theorem guard685 (p : Pattern) (guard : pushGuard support p 169 147 125 125 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound685 (p : Pattern) (guard : pushGuard support p 169 147 125 125 = true) : bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some 125)) := by
  have certified := compare1087 p (guard685 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 147 (some 125))
  have normalized := agree0 _ _ (change_representative support p 147 (some 125) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check685 (p : Pattern) : (!pushGuard support p 169 147 125 125 || decide (bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some 125)))) = true :=
  check_of_implication _ _ (bound685 p)
theorem guard686 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 191 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound686 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 191 .south = true) : bonus 169 p ≤ bonus 191 p := by
  have certified := compare1086 p (guard686 p guard)
  simpa only [at169, at191, Int.zero_add] using certified
theorem check686 (p : Pattern) : (!walkGuard soko2_2.board support p 169 191 .south || decide (bonus 169 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound686 p)
theorem guard687 (p : Pattern) (guard : pushGuard support p 169 191 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound687 (p : Pattern) (guard : pushGuard support p 169 191 213 213 = true) : bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder 213 - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some 213)) := by
  have certified := compare1087 p (guard687 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 191 (some 213))
  have normalized := agree0 _ _ (change_representative support p 191 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check687 (p : Pattern) : (!pushGuard support p 169 191 213 213 || decide (bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder 213 - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some 213)))) = true :=
  check_of_implication _ _ (bound687 p)
theorem guard688 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 170 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound688 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 170 .east = true) : bonus 169 p ≤ bonus 170 p := by
  have certified := compare1086 p (guard688 p guard)
  simpa only [at169, at170, Int.zero_add] using certified
theorem check688 (p : Pattern) : (!walkGuard soko2_2.board support p 169 170 .east || decide (bonus 169 p ≤ bonus 170 p)) = true :=
  check_of_implication _ _ (bound688 p)
theorem guard689 (p : Pattern) (guard : pushGuard support p 169 170 171 171 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound689 (p : Pattern) (guard : pushGuard support p 169 170 171 171 = true) : bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some 171)) := by
  have certified := compare1087 p (guard689 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 170 (some 171))
  have normalized := agree0 _ _ (change_representative support p 170 (some 171) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check689 (p : Pattern) : (!pushGuard support p 169 170 171 171 || decide (bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some 171)))) = true :=
  check_of_implication _ _ (bound689 p)
theorem guard690 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 168 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound690 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 168 .west = true) : bonus 169 p ≤ bonus 168 p := by
  have certified := compare1086 p (guard690 p guard)
  simpa only [at169, at168, Int.zero_add] using certified
theorem check690 (p : Pattern) : (!walkGuard soko2_2.board support p 169 168 .west || decide (bonus 169 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound690 p)
theorem guard691 (p : Pattern) (guard : pushGuard support p 169 168 167 167 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound691 (p : Pattern) (guard : pushGuard support p 169 168 167 167 = true) : bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some 167)) := by
  have certified := compare1087 p (guard691 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 168 (some 167))
  have normalized := agree0 _ _ (change_representative support p 168 (some 167) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check691 (p : Pattern) : (!pushGuard support p 169 168 167 167 || decide (bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some 167)))) = true :=
  check_of_implication _ _ (bound691 p)
theorem guard692 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 148 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound692 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 148 .northEast = true) : bonus 169 p ≤ bonus 148 p := by
  have certified := compare1086 p (guard692 p guard)
  simpa only [at169, at148, Int.zero_add] using certified
theorem check692 (p : Pattern) : (!walkGuard soko2_2.board support p 169 148 .northEast || decide (bonus 169 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound692 p)
theorem guard693 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 146 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound693 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 146 .northWest = true) : bonus 169 p ≤ bonus 146 p := by
  have certified := compare1086 p (guard693 p guard)
  simpa only [at169, at146, Int.zero_add] using certified
theorem check693 (p : Pattern) : (!walkGuard soko2_2.board support p 169 146 .northWest || decide (bonus 169 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound693 p)
theorem guard694 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 192 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound694 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 192 .southEast = true) : bonus 169 p ≤ bonus 192 p := by
  have certified := compare1086 p (guard694 p guard)
  simpa only [at169, at192, Int.zero_add] using certified
theorem check694 (p : Pattern) : (!walkGuard soko2_2.board support p 169 192 .southEast || decide (bonus 169 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound694 p)
theorem guard695 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 190 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound695 (p : Pattern) (guard : walkGuard soko2_2.board support p 169 190 .southWest = true) : bonus 169 p ≤ bonus 190 p := by
  have certified := compare1086 p (guard695 p guard)
  simpa only [at169, at190, Int.zero_add] using certified
theorem check695 (p : Pattern) : (!walkGuard soko2_2.board support p 169 190 .southWest || decide (bonus 169 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound695 p)
end NetHack.Sokoban22Refined85
