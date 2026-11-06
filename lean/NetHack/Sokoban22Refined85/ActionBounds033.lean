import NetHack.Sokoban22Refined85.ActionBounds032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard792 (p : Pattern) (guard : pushGuard support p 190 191 192 192 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound792 (p : Pattern) (guard : pushGuard support p 190 191 192 192 = true) : bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some 192)) := by
  have certified := compare1087 p (guard792 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 191 (some 192))
  have normalized := agree0 _ _ (change_representative support p 191 (some 192) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check792 (p : Pattern) : (!pushGuard support p 190 191 192 192 || decide (bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some 192)))) = true :=
  check_of_implication _ _ (bound792 p)
theorem guard793 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 189 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound793 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 189 .west = true) : bonus 190 p ≤ bonus 189 p := by
  have certified := compare1086 p (guard793 p guard)
  simpa only [at190, at189, Int.zero_add] using certified
theorem check793 (p : Pattern) : (!walkGuard soko2_2.board support p 190 189 .west || decide (bonus 190 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound793 p)
theorem guard794 (p : Pattern) (guard : pushGuard support p 190 189 188 188 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound794 (p : Pattern) (guard : pushGuard support p 190 189 188 188 = true) : bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder 188 - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some 188)) := by
  have certified := compare1087 p (guard794 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 189 (some 188))
  have normalized := agree0 _ _ (change_representative support p 189 (some 188) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check794 (p : Pattern) : (!pushGuard support p 190 189 188 188 || decide (bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder 188 - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some 188)))) = true :=
  check_of_implication _ _ (bound794 p)
theorem guard795 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 169 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound795 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 169 .northEast = true) : bonus 190 p ≤ bonus 169 p := by
  have certified := compare1086 p (guard795 p guard)
  simpa only [at190, at169, Int.zero_add] using certified
theorem check795 (p : Pattern) : (!walkGuard soko2_2.board support p 190 169 .northEast || decide (bonus 190 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound795 p)
theorem guard796 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 167 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound796 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 167 .northWest = true) : bonus 190 p ≤ bonus 167 p := by
  have certified := compare1086 p (guard796 p guard)
  simpa only [at190, at167, Int.zero_add] using certified
theorem check796 (p : Pattern) : (!walkGuard soko2_2.board support p 190 167 .northWest || decide (bonus 190 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound796 p)
theorem guard797 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 213 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound797 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 213 .southEast = true) : bonus 190 p ≤ bonus 213 p := by
  have certified := compare1086 p (guard797 p guard)
  simpa only [at190, at213, Int.zero_add] using certified
theorem check797 (p : Pattern) : (!walkGuard soko2_2.board support p 190 213 .southEast || decide (bonus 190 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound797 p)
theorem guard798 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 211 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound798 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 211 .southWest = true) : bonus 190 p ≤ bonus 211 p := by
  have certified := compare1086 p (guard798 p guard)
  simpa only [at190, at211, Int.zero_add] using certified
theorem check798 (p : Pattern) : (!walkGuard soko2_2.board support p 190 211 .southWest || decide (bonus 190 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound798 p)
theorem guard799 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 169 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound799 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 169 .north = true) : bonus 191 p ≤ bonus 169 p := by
  have certified := compare1086 p (guard799 p guard)
  simpa only [at191, at169, Int.zero_add] using certified
theorem check799 (p : Pattern) : (!walkGuard soko2_2.board support p 191 169 .north || decide (bonus 191 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound799 p)
theorem guard800 (p : Pattern) (guard : pushGuard support p 191 169 147 147 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound800 (p : Pattern) (guard : pushGuard support p 191 169 147 147 = true) : bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some 147)) := by
  have certified := compare1087 p (guard800 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 169 (some 147))
  have normalized := agree0 _ _ (change_representative support p 169 (some 147) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check800 (p : Pattern) : (!pushGuard support p 191 169 147 147 || decide (bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some 147)))) = true :=
  check_of_implication _ _ (bound800 p)
theorem guard801 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 213 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound801 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 213 .south = true) : bonus 191 p ≤ bonus 213 p := by
  have certified := compare1086 p (guard801 p guard)
  simpa only [at191, at213, Int.zero_add] using certified
theorem check801 (p : Pattern) : (!walkGuard soko2_2.board support p 191 213 .south || decide (bonus 191 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound801 p)
theorem guard802 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 192 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound802 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 192 .east = true) : bonus 191 p ≤ bonus 192 p := by
  have certified := compare1086 p (guard802 p guard)
  simpa only [at191, at192, Int.zero_add] using certified
theorem check802 (p : Pattern) : (!walkGuard soko2_2.board support p 191 192 .east || decide (bonus 191 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound802 p)
theorem guard803 (p : Pattern) (guard : pushGuard support p 191 192 193 193 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound803 (p : Pattern) (guard : pushGuard support p 191 192 193 193 = true) : bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder 193 - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some 193)) := by
  have certified := compare1087 p (guard803 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 192 (some 193))
  have normalized := agree0 _ _ (change_representative support p 192 (some 193) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check803 (p : Pattern) : (!pushGuard support p 191 192 193 193 || decide (bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder 193 - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some 193)))) = true :=
  check_of_implication _ _ (bound803 p)
theorem guard804 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 190 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound804 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 190 .west = true) : bonus 191 p ≤ bonus 190 p := by
  have certified := compare1086 p (guard804 p guard)
  simpa only [at191, at190, Int.zero_add] using certified
theorem check804 (p : Pattern) : (!walkGuard soko2_2.board support p 191 190 .west || decide (bonus 191 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound804 p)
theorem guard805 (p : Pattern) (guard : pushGuard support p 191 190 189 189 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound805 (p : Pattern) (guard : pushGuard support p 191 190 189 189 = true) : bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder 189 - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some 189)) := by
  have certified := compare1087 p (guard805 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 190 (some 189))
  have normalized := agree0 _ _ (change_representative support p 190 (some 189) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check805 (p : Pattern) : (!pushGuard support p 191 190 189 189 || decide (bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder 189 - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some 189)))) = true :=
  check_of_implication _ _ (bound805 p)
theorem guard806 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 170 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound806 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 170 .northEast = true) : bonus 191 p ≤ bonus 170 p := by
  have certified := compare1086 p (guard806 p guard)
  simpa only [at191, at170, Int.zero_add] using certified
theorem check806 (p : Pattern) : (!walkGuard soko2_2.board support p 191 170 .northEast || decide (bonus 191 p ≤ bonus 170 p)) = true :=
  check_of_implication _ _ (bound806 p)
theorem guard807 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 168 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound807 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 168 .northWest = true) : bonus 191 p ≤ bonus 168 p := by
  have certified := compare1086 p (guard807 p guard)
  simpa only [at191, at168, Int.zero_add] using certified
theorem check807 (p : Pattern) : (!walkGuard soko2_2.board support p 191 168 .northWest || decide (bonus 191 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound807 p)
theorem guard808 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 214 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound808 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 214 .southEast = true) : bonus 191 p ≤ bonus 214 p := by
  have certified := compare1086 p (guard808 p guard)
  simpa only [at191, at214, Int.zero_add] using certified
theorem check808 (p : Pattern) : (!walkGuard soko2_2.board support p 191 214 .southEast || decide (bonus 191 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound808 p)
theorem guard809 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 212 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound809 (p : Pattern) (guard : walkGuard soko2_2.board support p 191 212 .southWest = true) : bonus 191 p ≤ bonus 212 p := by
  have certified := compare1086 p (guard809 p guard)
  simpa only [at191, at212, Int.zero_add] using certified
theorem check809 (p : Pattern) : (!walkGuard soko2_2.board support p 191 212 .southWest || decide (bonus 191 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound809 p)
theorem guard810 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 170 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound810 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 170 .north = true) : bonus 192 p ≤ bonus 170 p := by
  have certified := compare1086 p (guard810 p guard)
  simpa only [at192, at170, Int.zero_add] using certified
theorem check810 (p : Pattern) : (!walkGuard soko2_2.board support p 192 170 .north || decide (bonus 192 p ≤ bonus 170 p)) = true :=
  check_of_implication _ _ (bound810 p)
theorem guard811 (p : Pattern) (guard : pushGuard support p 192 170 148 148 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound811 (p : Pattern) (guard : pushGuard support p 192 170 148 148 = true) : bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some 148)) := by
  have certified := compare1087 p (guard811 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 170 (some 148))
  have normalized := agree0 _ _ (change_representative support p 170 (some 148) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check811 (p : Pattern) : (!pushGuard support p 192 170 148 148 || decide (bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some 148)))) = true :=
  check_of_implication _ _ (bound811 p)
theorem guard812 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 214 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound812 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 214 .south = true) : bonus 192 p ≤ bonus 214 p := by
  have certified := compare1086 p (guard812 p guard)
  simpa only [at192, at214, Int.zero_add] using certified
theorem check812 (p : Pattern) : (!walkGuard soko2_2.board support p 192 214 .south || decide (bonus 192 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound812 p)
theorem guard813 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 193 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound813 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 193 .east = true) : bonus 192 p ≤ bonus 193 p := by
  have certified := compare1086 p (guard813 p guard)
  simpa only [at192, at193, Int.zero_add] using certified
theorem check813 (p : Pattern) : (!walkGuard soko2_2.board support p 192 193 .east || decide (bonus 192 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound813 p)
theorem guard814 (p : Pattern) (guard : pushGuard support p 192 193 194 194 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound814 (p : Pattern) (guard : pushGuard support p 192 193 194 194 = true) : bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder 194 - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some 194)) := by
  have certified := compare1087 p (guard814 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 193 (some 194))
  have normalized := agree0 _ _ (change_representative support p 193 (some 194) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check814 (p : Pattern) : (!pushGuard support p 192 193 194 194 || decide (bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder 194 - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some 194)))) = true :=
  check_of_implication _ _ (bound814 p)
theorem guard815 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 191 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound815 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 191 .west = true) : bonus 192 p ≤ bonus 191 p := by
  have certified := compare1086 p (guard815 p guard)
  simpa only [at192, at191, Int.zero_add] using certified
theorem check815 (p : Pattern) : (!walkGuard soko2_2.board support p 192 191 .west || decide (bonus 192 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound815 p)
end NetHack.Sokoban22Refined85
