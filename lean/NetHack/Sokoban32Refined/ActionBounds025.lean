import NetHack.Sokoban32Refined.ActionBounds024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard600 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 175 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound600 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 175 .south = true) : bonus 149 p ≤ bonus 175 p := by
  have certified := compare103 p (guard600 p guard)
  simpa only [at149, at175, Int.zero_add] using certified
theorem check600 (p : Pattern) : (!walkGuard soko3_2.board support p 149 175 .south || decide (bonus 149 p ≤ bonus 175 p)) = true :=
  check_of_implication _ _ (bound600 p)
theorem guard601 (p : Pattern) (guard : pushGuard support p 149 175 201 201 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound601 (p : Pattern) (guard : pushGuard support p 149 175 201 201 = true) : bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some 201)) := by
  have certified := compare37 p (guard601 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 175 (some 201))
  have normalized := agree0 _ _ (change_representative support p 175 (some 201) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check601 (p : Pattern) : (!pushGuard support p 149 175 201 201 || decide (bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some 201)))) = true :=
  check_of_implication _ _ (bound601 p)
theorem guard602 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 150 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound602 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 150 .east = true) : bonus 149 p ≤ bonus 150 p := by
  have certified := compare103 p (guard602 p guard)
  simpa only [at149, at150, Int.zero_add] using certified
theorem check602 (p : Pattern) : (!walkGuard soko3_2.board support p 149 150 .east || decide (bonus 149 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound602 p)
theorem guard603 (p : Pattern) (guard : pushGuard support p 149 150 151 151 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound603 (p : Pattern) (guard : pushGuard support p 149 150 151 151 = true) : bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some 151)) := by
  have certified := compare37 p (guard603 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 150 (some 151))
  have normalized := agree0 _ _ (change_representative support p 150 (some 151) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check603 (p : Pattern) : (!pushGuard support p 149 150 151 151 || decide (bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some 151)))) = true :=
  check_of_implication _ _ (bound603 p)
theorem guard604 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 148 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound604 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 148 .west = true) : bonus 149 p ≤ bonus 148 p := by
  have certified := compare103 p (guard604 p guard)
  simpa only [at149, at148, Int.zero_add] using certified
theorem check604 (p : Pattern) : (!walkGuard soko3_2.board support p 149 148 .west || decide (bonus 149 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound604 p)
theorem guard605 (p : Pattern) (guard : pushGuard support p 149 148 147 147 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound605 (p : Pattern) (guard : pushGuard support p 149 148 147 147 = true) : bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some 147)) := by
  have certified := compare37 p (guard605 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 148 (some 147))
  have normalized := agree0 _ _ (change_representative support p 148 (some 147) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check605 (p : Pattern) : (!pushGuard support p 149 148 147 147 || decide (bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some 147)))) = true :=
  check_of_implication _ _ (bound605 p)
theorem guard606 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 124 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound606 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 124 .northEast = true) : bonus 149 p ≤ bonus 124 p := by
  have certified := compare103 p (guard606 p guard)
  simpa only [at149, at124, Int.zero_add] using certified
theorem check606 (p : Pattern) : (!walkGuard soko3_2.board support p 149 124 .northEast || decide (bonus 149 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound606 p)
theorem guard607 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 122 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound607 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 122 .northWest = true) : bonus 149 p ≤ bonus 122 p := by
  have certified := compare103 p (guard607 p guard)
  simpa only [at149, at122, Int.zero_add] using certified
theorem check607 (p : Pattern) : (!walkGuard soko3_2.board support p 149 122 .northWest || decide (bonus 149 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound607 p)
theorem guard608 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 176 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound608 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 176 .southEast = true) : bonus 149 p ≤ bonus 176 p := by
  have certified := compare103 p (guard608 p guard)
  simpa only [at149, at176, Int.zero_add] using certified
theorem check608 (p : Pattern) : (!walkGuard soko3_2.board support p 149 176 .southEast || decide (bonus 149 p ≤ bonus 176 p)) = true :=
  check_of_implication _ _ (bound608 p)
theorem guard609 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 174 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound609 (p : Pattern) (guard : walkGuard soko3_2.board support p 149 174 .southWest = true) : bonus 149 p ≤ bonus 174 p := by
  have certified := compare103 p (guard609 p guard)
  simpa only [at149, at174, Int.zero_add] using certified
theorem check609 (p : Pattern) : (!walkGuard soko3_2.board support p 149 174 .southWest || decide (bonus 149 p ≤ bonus 174 p)) = true :=
  check_of_implication _ _ (bound609 p)
theorem guard610 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 124 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound610 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 124 .north = true) : bonus 150 p ≤ bonus 124 p := by
  have certified := compare103 p (guard610 p guard)
  simpa only [at150, at124, Int.zero_add] using certified
theorem check610 (p : Pattern) : (!walkGuard soko3_2.board support p 150 124 .north || decide (bonus 150 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound610 p)
theorem guard611 (p : Pattern) (guard : pushGuard support p 150 124 98 98 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound611 (p : Pattern) (guard : pushGuard support p 150 124 98 98 = true) : bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some 98)) := by
  have certified := compare37 p (guard611 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 124 (some 98))
  have normalized := agree0 _ _ (change_representative support p 124 (some 98) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check611 (p : Pattern) : (!pushGuard support p 150 124 98 98 || decide (bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some 98)))) = true :=
  check_of_implication _ _ (bound611 p)
theorem guard612 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 176 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound612 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 176 .south = true) : bonus 150 p ≤ bonus 176 p := by
  have certified := compare103 p (guard612 p guard)
  simpa only [at150, at176, Int.zero_add] using certified
theorem check612 (p : Pattern) : (!walkGuard soko3_2.board support p 150 176 .south || decide (bonus 150 p ≤ bonus 176 p)) = true :=
  check_of_implication _ _ (bound612 p)
theorem guard613 (p : Pattern) (guard : pushGuard support p 150 176 202 202 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound613 (p : Pattern) (guard : pushGuard support p 150 176 202 202 = true) : bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some 202)) := by
  have certified := compare37 p (guard613 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 176 (some 202))
  have normalized := agree0 _ _ (change_representative support p 176 (some 202) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check613 (p : Pattern) : (!pushGuard support p 150 176 202 202 || decide (bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some 202)))) = true :=
  check_of_implication _ _ (bound613 p)
theorem guard614 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 151 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound614 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 151 .east = true) : bonus 150 p ≤ bonus 151 p := by
  have certified := compare103 p (guard614 p guard)
  simpa only [at150, at151, Int.zero_add] using certified
theorem check614 (p : Pattern) : (!walkGuard soko3_2.board support p 150 151 .east || decide (bonus 150 p ≤ bonus 151 p)) = true :=
  check_of_implication _ _ (bound614 p)
theorem guard615 (p : Pattern) (guard : pushGuard support p 150 151 152 152 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound615 (p : Pattern) (guard : pushGuard support p 150 151 152 152 = true) : bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some 152)) := by
  have certified := compare37 p (guard615 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 151 (some 152))
  have normalized := agree0 _ _ (change_representative support p 151 (some 152) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check615 (p : Pattern) : (!pushGuard support p 150 151 152 152 || decide (bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some 152)))) = true :=
  check_of_implication _ _ (bound615 p)
theorem guard616 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 149 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound616 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 149 .west = true) : bonus 150 p ≤ bonus 149 p := by
  have certified := compare103 p (guard616 p guard)
  simpa only [at150, at149, Int.zero_add] using certified
theorem check616 (p : Pattern) : (!walkGuard soko3_2.board support p 150 149 .west || decide (bonus 150 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound616 p)
theorem guard617 (p : Pattern) (guard : pushGuard support p 150 149 148 148 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound617 (p : Pattern) (guard : pushGuard support p 150 149 148 148 = true) : bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some 148)) := by
  have certified := compare37 p (guard617 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 149 (some 148))
  have normalized := agree0 _ _ (change_representative support p 149 (some 148) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check617 (p : Pattern) : (!pushGuard support p 150 149 148 148 || decide (bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some 148)))) = true :=
  check_of_implication _ _ (bound617 p)
theorem guard618 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 125 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound618 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 125 .northEast = true) : bonus 150 p ≤ bonus 125 p := by
  have certified := compare103 p (guard618 p guard)
  simpa only [at150, at125, Int.zero_add] using certified
theorem check618 (p : Pattern) : (!walkGuard soko3_2.board support p 150 125 .northEast || decide (bonus 150 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound618 p)
theorem guard619 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 123 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound619 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 123 .northWest = true) : bonus 150 p ≤ bonus 123 p := by
  have certified := compare103 p (guard619 p guard)
  simpa only [at150, at123, Int.zero_add] using certified
theorem check619 (p : Pattern) : (!walkGuard soko3_2.board support p 150 123 .northWest || decide (bonus 150 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound619 p)
theorem guard620 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 177 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound620 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 177 .southEast = true) : bonus 150 p ≤ bonus 177 p := by
  have certified := compare103 p (guard620 p guard)
  simpa only [at150, at177, Int.zero_add] using certified
theorem check620 (p : Pattern) : (!walkGuard soko3_2.board support p 150 177 .southEast || decide (bonus 150 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound620 p)
theorem guard621 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 175 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound621 (p : Pattern) (guard : walkGuard soko3_2.board support p 150 175 .southWest = true) : bonus 150 p ≤ bonus 175 p := by
  have certified := compare103 p (guard621 p guard)
  simpa only [at150, at175, Int.zero_add] using certified
theorem check621 (p : Pattern) : (!walkGuard soko3_2.board support p 150 175 .southWest || decide (bonus 150 p ≤ bonus 175 p)) = true :=
  check_of_implication _ _ (bound621 p)
theorem guard622 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 125 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound622 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 125 .north = true) : bonus 151 p ≤ bonus 125 p := by
  have certified := compare103 p (guard622 p guard)
  simpa only [at151, at125, Int.zero_add] using certified
theorem check622 (p : Pattern) : (!walkGuard soko3_2.board support p 151 125 .north || decide (bonus 151 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound622 p)
theorem guard623 (p : Pattern) (guard : pushGuard support p 151 125 99 99 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound623 (p : Pattern) (guard : pushGuard support p 151 125 99 99 = true) : bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some 99)) := by
  have certified := compare37 p (guard623 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 125 (some 99))
  have normalized := agree0 _ _ (change_representative support p 125 (some 99) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check623 (p : Pattern) : (!pushGuard support p 151 125 99 99 || decide (bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some 99)))) = true :=
  check_of_implication _ _ (bound623 p)
end NetHack.Sokoban32Refined
