import NetHack.Sokoban32Refined.ActionBounds032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard792 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 176 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound792 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 176 .west = true) : bonus 177 p ≤ bonus 176 p := by
  have certified := compare103 p (guard792 p guard)
  simpa only [at177, at176, Int.zero_add] using certified
theorem check792 (p : Pattern) : (!walkGuard soko3_2.board support p 177 176 .west || decide (bonus 177 p ≤ bonus 176 p)) = true :=
  check_of_implication _ _ (bound792 p)
theorem guard793 (p : Pattern) (guard : pushGuard support p 177 176 175 175 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound793 (p : Pattern) (guard : pushGuard support p 177 176 175 175 = true) : bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some 175)) := by
  have certified := compare37 p (guard793 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 176 (some 175))
  have normalized := agree0 _ _ (change_representative support p 176 (some 175) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check793 (p : Pattern) : (!pushGuard support p 177 176 175 175 || decide (bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some 175)))) = true :=
  check_of_implication _ _ (bound793 p)
theorem guard794 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 152 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound794 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 152 .northEast = true) : bonus 177 p ≤ bonus 152 p := by
  have certified := compare103 p (guard794 p guard)
  simpa only [at177, at152, Int.zero_add] using certified
theorem check794 (p : Pattern) : (!walkGuard soko3_2.board support p 177 152 .northEast || decide (bonus 177 p ≤ bonus 152 p)) = true :=
  check_of_implication _ _ (bound794 p)
theorem guard795 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 150 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound795 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 150 .northWest = true) : bonus 177 p ≤ bonus 150 p := by
  have certified := compare103 p (guard795 p guard)
  simpa only [at177, at150, Int.zero_add] using certified
theorem check795 (p : Pattern) : (!walkGuard soko3_2.board support p 177 150 .northWest || decide (bonus 177 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound795 p)
theorem guard796 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 204 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound796 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 204 .southEast = true) : bonus 177 p ≤ bonus 204 p := by
  have certified := compare103 p (guard796 p guard)
  simpa only [at177, at204, Int.zero_add] using certified
theorem check796 (p : Pattern) : (!walkGuard soko3_2.board support p 177 204 .southEast || decide (bonus 177 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound796 p)
theorem guard797 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 202 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound797 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 202 .southWest = true) : bonus 177 p ≤ bonus 202 p := by
  have certified := compare103 p (guard797 p guard)
  simpa only [at177, at202, Int.zero_add] using certified
theorem check797 (p : Pattern) : (!walkGuard soko3_2.board support p 177 202 .southWest || decide (bonus 177 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound797 p)
theorem guard798 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 152 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound798 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 152 .north = true) : bonus 178 p ≤ bonus 152 p := by
  have certified := compare103 p (guard798 p guard)
  simpa only [at178, at152, Int.zero_add] using certified
theorem check798 (p : Pattern) : (!walkGuard soko3_2.board support p 178 152 .north || decide (bonus 178 p ≤ bonus 152 p)) = true :=
  check_of_implication _ _ (bound798 p)
theorem guard799 (p : Pattern) (guard : pushGuard support p 178 152 126 126 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound799 (p : Pattern) (guard : pushGuard support p 178 152 126 126 = true) : bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some 126)) := by
  have certified := compare37 p (guard799 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 152 (some 126))
  have normalized := agree0 _ _ (change_representative support p 152 (some 126) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check799 (p : Pattern) : (!pushGuard support p 178 152 126 126 || decide (bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some 126)))) = true :=
  check_of_implication _ _ (bound799 p)
theorem guard800 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 204 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound800 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 204 .south = true) : bonus 178 p ≤ bonus 204 p := by
  have certified := compare103 p (guard800 p guard)
  simpa only [at178, at204, Int.zero_add] using certified
theorem check800 (p : Pattern) : (!walkGuard soko3_2.board support p 178 204 .south || decide (bonus 178 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound800 p)
theorem guard801 (p : Pattern) (guard : pushGuard support p 178 204 230 230 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound801 (p : Pattern) (guard : pushGuard support p 178 204 230 230 = true) : bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder 230 - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some 230)) := by
  have certified := compare37 p (guard801 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 204 (some 230))
  have normalized := agree0 _ _ (change_representative support p 204 (some 230) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check801 (p : Pattern) : (!pushGuard support p 178 204 230 230 || decide (bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder 230 - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some 230)))) = true :=
  check_of_implication _ _ (bound801 p)
theorem guard802 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 179 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound802 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 179 .east = true) : bonus 178 p ≤ bonus 179 p := by
  have certified := compare103 p (guard802 p guard)
  simpa only [at178, at179, Int.zero_add] using certified
theorem check802 (p : Pattern) : (!walkGuard soko3_2.board support p 178 179 .east || decide (bonus 178 p ≤ bonus 179 p)) = true :=
  check_of_implication _ _ (bound802 p)
theorem guard803 (p : Pattern) (guard : pushGuard support p 178 179 180 180 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound803 (p : Pattern) (guard : pushGuard support p 178 179 180 180 = true) : bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder 180 - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some 180)) := by
  have certified := compare37 p (guard803 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 179 (some 180))
  have normalized := agree0 _ _ (change_representative support p 179 (some 180) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check803 (p : Pattern) : (!pushGuard support p 178 179 180 180 || decide (bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder 180 - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some 180)))) = true :=
  check_of_implication _ _ (bound803 p)
theorem guard804 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 177 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound804 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 177 .west = true) : bonus 178 p ≤ bonus 177 p := by
  have certified := compare103 p (guard804 p guard)
  simpa only [at178, at177, Int.zero_add] using certified
theorem check804 (p : Pattern) : (!walkGuard soko3_2.board support p 178 177 .west || decide (bonus 178 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound804 p)
theorem guard805 (p : Pattern) (guard : pushGuard support p 178 177 176 176 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound805 (p : Pattern) (guard : pushGuard support p 178 177 176 176 = true) : bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some 176)) := by
  have certified := compare37 p (guard805 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 177 (some 176))
  have normalized := agree0 _ _ (change_representative support p 177 (some 176) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check805 (p : Pattern) : (!pushGuard support p 178 177 176 176 || decide (bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some 176)))) = true :=
  check_of_implication _ _ (bound805 p)
theorem guard806 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 153 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound806 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 153 .northEast = true) : bonus 178 p ≤ bonus 153 p := by
  have certified := compare103 p (guard806 p guard)
  simpa only [at178, at153, Int.zero_add] using certified
theorem check806 (p : Pattern) : (!walkGuard soko3_2.board support p 178 153 .northEast || decide (bonus 178 p ≤ bonus 153 p)) = true :=
  check_of_implication _ _ (bound806 p)
theorem guard807 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 151 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound807 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 151 .northWest = true) : bonus 178 p ≤ bonus 151 p := by
  have certified := compare103 p (guard807 p guard)
  simpa only [at178, at151, Int.zero_add] using certified
theorem check807 (p : Pattern) : (!walkGuard soko3_2.board support p 178 151 .northWest || decide (bonus 178 p ≤ bonus 151 p)) = true :=
  check_of_implication _ _ (bound807 p)
theorem guard808 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 205 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound808 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 205 .southEast = true) : bonus 178 p ≤ bonus 205 p := by
  have certified := compare103 p (guard808 p guard)
  simpa only [at178, at205, Int.zero_add] using certified
theorem check808 (p : Pattern) : (!walkGuard soko3_2.board support p 178 205 .southEast || decide (bonus 178 p ≤ bonus 205 p)) = true :=
  check_of_implication _ _ (bound808 p)
theorem guard809 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 203 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound809 (p : Pattern) (guard : walkGuard soko3_2.board support p 178 203 .southWest = true) : bonus 178 p ≤ bonus 203 p := by
  have certified := compare103 p (guard809 p guard)
  simpa only [at178, at203, Int.zero_add] using certified
theorem check809 (p : Pattern) : (!walkGuard soko3_2.board support p 178 203 .southWest || decide (bonus 178 p ≤ bonus 203 p)) = true :=
  check_of_implication _ _ (bound809 p)
theorem guard810 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 153 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound810 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 153 .north = true) : bonus 179 p ≤ bonus 153 p := by
  have certified := compare103 p (guard810 p guard)
  simpa only [at179, at153, Int.zero_add] using certified
theorem check810 (p : Pattern) : (!walkGuard soko3_2.board support p 179 153 .north || decide (bonus 179 p ≤ bonus 153 p)) = true :=
  check_of_implication _ _ (bound810 p)
theorem guard811 (p : Pattern) (guard : pushGuard support p 179 153 127 127 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound811 (p : Pattern) (guard : pushGuard support p 179 153 127 127 = true) : bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some 127)) := by
  have certified := compare37 p (guard811 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 153 (some 127))
  have normalized := agree0 _ _ (change_representative support p 153 (some 127) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check811 (p : Pattern) : (!pushGuard support p 179 153 127 127 || decide (bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some 127)))) = true :=
  check_of_implication _ _ (bound811 p)
theorem guard812 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 205 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound812 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 205 .south = true) : bonus 179 p ≤ bonus 205 p := by
  have certified := compare103 p (guard812 p guard)
  simpa only [at179, at205, Int.zero_add] using certified
theorem check812 (p : Pattern) : (!walkGuard soko3_2.board support p 179 205 .south || decide (bonus 179 p ≤ bonus 205 p)) = true :=
  check_of_implication _ _ (bound812 p)
theorem guard813 (p : Pattern) (guard : pushGuard support p 179 205 231 231 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound813 (p : Pattern) (guard : pushGuard support p 179 205 231 231 = true) : bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder 231 - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some 231)) := by
  have certified := compare37 p (guard813 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 205 (some 231))
  have normalized := agree0 _ _ (change_representative support p 205 (some 231) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check813 (p : Pattern) : (!pushGuard support p 179 205 231 231 || decide (bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder 231 - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some 231)))) = true :=
  check_of_implication _ _ (bound813 p)
theorem guard814 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 180 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound814 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 180 .east = true) : bonus 179 p ≤ bonus 180 p := by
  have certified := compare103 p (guard814 p guard)
  simpa only [at179, at180, Int.zero_add] using certified
theorem check814 (p : Pattern) : (!walkGuard soko3_2.board support p 179 180 .east || decide (bonus 179 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound814 p)
theorem guard815 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 178 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound815 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 178 .west = true) : bonus 179 p ≤ bonus 178 p := by
  have certified := compare103 p (guard815 p guard)
  simpa only [at179, at178, Int.zero_add] using certified
theorem check815 (p : Pattern) : (!walkGuard soko3_2.board support p 179 178 .west || decide (bonus 179 p ≤ bonus 178 p)) = true :=
  check_of_implication _ _ (bound815 p)
end NetHack.Sokoban32Refined
