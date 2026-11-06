import NetHack.Sokoban32Refined.ActionBounds033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard816 (p : Pattern) (guard : pushGuard support p 179 178 177 177 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound816 (p : Pattern) (guard : pushGuard support p 179 178 177 177 = true) : bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some 177)) := by
  have certified := compare37 p (guard816 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 178 (some 177))
  have normalized := agree0 _ _ (change_representative support p 178 (some 177) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check816 (p : Pattern) : (!pushGuard support p 179 178 177 177 || decide (bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some 177)))) = true :=
  check_of_implication _ _ (bound816 p)
theorem guard817 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 154 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound817 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 154 .northEast = true) : bonus 179 p ≤ bonus 154 p := by
  have certified := compare103 p (guard817 p guard)
  simpa only [at179, at154, Int.zero_add] using certified
theorem check817 (p : Pattern) : (!walkGuard soko3_2.board support p 179 154 .northEast || decide (bonus 179 p ≤ bonus 154 p)) = true :=
  check_of_implication _ _ (bound817 p)
theorem guard818 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 152 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound818 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 152 .northWest = true) : bonus 179 p ≤ bonus 152 p := by
  have certified := compare103 p (guard818 p guard)
  simpa only [at179, at152, Int.zero_add] using certified
theorem check818 (p : Pattern) : (!walkGuard soko3_2.board support p 179 152 .northWest || decide (bonus 179 p ≤ bonus 152 p)) = true :=
  check_of_implication _ _ (bound818 p)
theorem guard819 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 206 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound819 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 206 .southEast = true) : bonus 179 p ≤ bonus 206 p := by
  have certified := compare103 p (guard819 p guard)
  simpa only [at179, at206, Int.zero_add] using certified
theorem check819 (p : Pattern) : (!walkGuard soko3_2.board support p 179 206 .southEast || decide (bonus 179 p ≤ bonus 206 p)) = true :=
  check_of_implication _ _ (bound819 p)
theorem guard820 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 204 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound820 (p : Pattern) (guard : walkGuard soko3_2.board support p 179 204 .southWest = true) : bonus 179 p ≤ bonus 204 p := by
  have certified := compare103 p (guard820 p guard)
  simpa only [at179, at204, Int.zero_add] using certified
theorem check820 (p : Pattern) : (!walkGuard soko3_2.board support p 179 204 .southWest || decide (bonus 179 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound820 p)
theorem guard821 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 154 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound821 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 154 .north = true) : bonus 180 p ≤ bonus 154 p := by
  have certified := compare103 p (guard821 p guard)
  simpa only [at180, at154, Int.zero_add] using certified
theorem check821 (p : Pattern) : (!walkGuard soko3_2.board support p 180 154 .north || decide (bonus 180 p ≤ bonus 154 p)) = true :=
  check_of_implication _ _ (bound821 p)
theorem guard822 (p : Pattern) (guard : pushGuard support p 180 154 128 128 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound822 (p : Pattern) (guard : pushGuard support p 180 154 128 128 = true) : bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder 128 - Generated.soko3_2Potential.boulder 154 + bonus 154 (change p 154 (some 128)) := by
  have certified := compare37 p (guard822 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 154 (some 128))
  have normalized := agree0 _ _ (change_representative support p 154 (some 128) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check822 (p : Pattern) : (!pushGuard support p 180 154 128 128 || decide (bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder 128 - Generated.soko3_2Potential.boulder 154 + bonus 154 (change p 154 (some 128)))) = true :=
  check_of_implication _ _ (bound822 p)
theorem guard823 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 206 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound823 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 206 .south = true) : bonus 180 p ≤ bonus 206 p := by
  have certified := compare103 p (guard823 p guard)
  simpa only [at180, at206, Int.zero_add] using certified
theorem check823 (p : Pattern) : (!walkGuard soko3_2.board support p 180 206 .south || decide (bonus 180 p ≤ bonus 206 p)) = true :=
  check_of_implication _ _ (bound823 p)
theorem guard824 (p : Pattern) (guard : pushGuard support p 180 206 232 232 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound824 (p : Pattern) (guard : pushGuard support p 180 206 232 232 = true) : bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder 232 - Generated.soko3_2Potential.boulder 206 + bonus 206 (change p 206 (some 232)) := by
  have certified := compare37 p (guard824 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 206 (some 232))
  have normalized := agree0 _ _ (change_representative support p 206 (some 232) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check824 (p : Pattern) : (!pushGuard support p 180 206 232 232 || decide (bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder 232 - Generated.soko3_2Potential.boulder 206 + bonus 206 (change p 206 (some 232)))) = true :=
  check_of_implication _ _ (bound824 p)
theorem guard825 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 179 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound825 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 179 .west = true) : bonus 180 p ≤ bonus 179 p := by
  have certified := compare103 p (guard825 p guard)
  simpa only [at180, at179, Int.zero_add] using certified
theorem check825 (p : Pattern) : (!walkGuard soko3_2.board support p 180 179 .west || decide (bonus 180 p ≤ bonus 179 p)) = true :=
  check_of_implication _ _ (bound825 p)
theorem guard826 (p : Pattern) (guard : pushGuard support p 180 179 178 178 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound826 (p : Pattern) (guard : pushGuard support p 180 179 178 178 = true) : bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some 178)) := by
  have certified := compare37 p (guard826 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 179 (some 178))
  have normalized := agree0 _ _ (change_representative support p 179 (some 178) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check826 (p : Pattern) : (!pushGuard support p 180 179 178 178 || decide (bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some 178)))) = true :=
  check_of_implication _ _ (bound826 p)
theorem guard827 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 153 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound827 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 153 .northWest = true) : bonus 180 p ≤ bonus 153 p := by
  have certified := compare103 p (guard827 p guard)
  simpa only [at180, at153, Int.zero_add] using certified
theorem check827 (p : Pattern) : (!walkGuard soko3_2.board support p 180 153 .northWest || decide (bonus 180 p ≤ bonus 153 p)) = true :=
  check_of_implication _ _ (bound827 p)
theorem guard828 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 205 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound828 (p : Pattern) (guard : walkGuard soko3_2.board support p 180 205 .southWest = true) : bonus 180 p ≤ bonus 205 p := by
  have certified := compare103 p (guard828 p guard)
  simpa only [at180, at205, Int.zero_add] using certified
theorem check828 (p : Pattern) : (!walkGuard soko3_2.board support p 180 205 .southWest || decide (bonus 180 p ≤ bonus 205 p)) = true :=
  check_of_implication _ _ (bound828 p)
theorem guard829 (p : Pattern) (guard : walkGuard soko3_2.board support p 183 157 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound829 (p : Pattern) (guard : walkGuard soko3_2.board support p 183 157 .north = true) : bonus 183 p ≤ bonus 157 p := by
  have certified := compare0 p (guard829 p guard)
  simpa only [at183, at157, Int.zero_add] using certified
theorem check829 (p : Pattern) : (!walkGuard soko3_2.board support p 183 157 .north || decide (bonus 183 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound829 p)
theorem guard830 (p : Pattern) (guard : pushGuard support p 183 157 131 131 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound830 (p : Pattern) (guard : pushGuard support p 183 157 131 131 = true) : bonus 183 p ≤ 1 + Generated.soko3_2Potential.boulder 131 - Generated.soko3_2Potential.boulder 157 + bonus 157 (change p 157 (some 131)) := by
  have certified := compare104 p (guard830 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 157 (some 131))
  have normalized := agree134 _ _ (change_representative support p 157 (some 131) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check830 (p : Pattern) : (!pushGuard support p 183 157 131 131 || decide (bonus 183 p ≤ 1 + Generated.soko3_2Potential.boulder 131 - Generated.soko3_2Potential.boulder 157 + bonus 157 (change p 157 (some 131)))) = true :=
  check_of_implication _ _ (bound830 p)
theorem guard831 (p : Pattern) (guard : walkGuard soko3_2.board support p 183 209 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound831 (p : Pattern) (guard : walkGuard soko3_2.board support p 183 209 .south = true) : bonus 183 p ≤ bonus 209 p := by
  have certified := compare0 p (guard831 p guard)
  simpa only [at183, at209, Int.zero_add] using certified
theorem check831 (p : Pattern) : (!walkGuard soko3_2.board support p 183 209 .south || decide (bonus 183 p ≤ bonus 209 p)) = true :=
  check_of_implication _ _ (bound831 p)
theorem guard832 (p : Pattern) (guard : pushGuard support p 183 209 235 235 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound832 (p : Pattern) (guard : pushGuard support p 183 209 235 235 = true) : bonus 183 p ≤ 1 + Generated.soko3_2Potential.boulder 235 - Generated.soko3_2Potential.boulder 209 + bonus 209 (change p 209 (some 235)) := by
  have certified := compare104 p (guard832 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 209 (some 235))
  have normalized := agree134 _ _ (change_representative support p 209 (some 235) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check832 (p : Pattern) : (!pushGuard support p 183 209 235 235 || decide (bonus 183 p ≤ 1 + Generated.soko3_2Potential.boulder 235 - Generated.soko3_2Potential.boulder 209 + bonus 209 (change p 209 (some 235)))) = true :=
  check_of_implication _ _ (bound832 p)
theorem guard833 (p : Pattern) (guard : walkGuard soko3_2.board support p 183 158 .northEast = true) : d873 p = 1 := by
  change (!false && !(p 158) && !(true && false && true)) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d873, h158] at guard ⊢
theorem bound833 (p : Pattern) (guard : walkGuard soko3_2.board support p 183 158 .northEast = true) : bonus 183 p ≤ bonus 158 p := by
  have certified := compare2491 p (guard833 p guard)
  simpa only [at183, at158, Int.zero_add] using certified
theorem check833 (p : Pattern) : (!walkGuard soko3_2.board support p 183 158 .northEast || decide (bonus 183 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound833 p)
theorem guard834 (p : Pattern) (guard : walkGuard soko3_2.board support p 183 210 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound834 (p : Pattern) (guard : walkGuard soko3_2.board support p 183 210 .southEast = true) : bonus 183 p ≤ bonus 210 p := by
  have certified := compare0 p (guard834 p guard)
  simpa only [at183, at210, Int.zero_add] using certified
theorem check834 (p : Pattern) : (!walkGuard soko3_2.board support p 183 210 .southEast || decide (bonus 183 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound834 p)
theorem guard835 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 162 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound835 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 162 .north = true) : bonus 188 p ≤ bonus 162 p := by
  have certified := compare0 p (guard835 p guard)
  simpa only [at188, at162, Int.zero_add] using certified
theorem check835 (p : Pattern) : (!walkGuard soko3_2.board support p 188 162 .north || decide (bonus 188 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound835 p)
theorem guard836 (p : Pattern) (guard : pushGuard support p 188 162 136 136 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound836 (p : Pattern) (guard : pushGuard support p 188 162 136 136 = true) : bonus 188 p ≤ 1 + Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some 136)) := by
  have certified := compare4301 p (guard836 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 162 (some 136))
  have normalized := agree134 _ _ (change_representative support p 162 (some 136) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check836 (p : Pattern) : (!pushGuard support p 188 162 136 136 || decide (bonus 188 p ≤ 1 + Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some 136)))) = true :=
  check_of_implication _ _ (bound836 p)
theorem guard837 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 214 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound837 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 214 .south = true) : bonus 188 p ≤ bonus 214 p := by
  have certified := compare0 p (guard837 p guard)
  simpa only [at188, at214, Int.zero_add] using certified
theorem check837 (p : Pattern) : (!walkGuard soko3_2.board support p 188 214 .south || decide (bonus 188 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound837 p)
theorem guard838 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 189 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound838 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 189 .east = true) : bonus 188 p ≤ bonus 189 p := by
  have certified := compare0 p (guard838 p guard)
  simpa only [at188, at189, Int.zero_add] using certified
theorem check838 (p : Pattern) : (!walkGuard soko3_2.board support p 188 189 .east || decide (bonus 188 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound838 p)
theorem guard839 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 163 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound839 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 163 .northEast = true) : bonus 188 p ≤ bonus 163 p := by
  have certified := compare0 p (guard839 p guard)
  simpa only [at188, at163, Int.zero_add] using certified
theorem check839 (p : Pattern) : (!walkGuard soko3_2.board support p 188 163 .northEast || decide (bonus 188 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound839 p)
end NetHack.Sokoban32Refined
