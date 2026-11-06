import NetHack.Sokoban22Refined85.ActionBounds033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard816 (p : Pattern) (guard : pushGuard support p 192 191 190 190 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound816 (p : Pattern) (guard : pushGuard support p 192 191 190 190 = true) : bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some 190)) := by
  have certified := compare1087 p (guard816 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 191 (some 190))
  have normalized := agree0 _ _ (change_representative support p 191 (some 190) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check816 (p : Pattern) : (!pushGuard support p 192 191 190 190 || decide (bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some 190)))) = true :=
  check_of_implication _ _ (bound816 p)
theorem guard817 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 171 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound817 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 171 .northEast = true) : bonus 192 p ≤ bonus 171 p := by
  have certified := compare1086 p (guard817 p guard)
  simpa only [at192, at171, Int.zero_add] using certified
theorem check817 (p : Pattern) : (!walkGuard soko2_2.board support p 192 171 .northEast || decide (bonus 192 p ≤ bonus 171 p)) = true :=
  check_of_implication _ _ (bound817 p)
theorem guard818 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 169 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound818 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 169 .northWest = true) : bonus 192 p ≤ bonus 169 p := by
  have certified := compare1086 p (guard818 p guard)
  simpa only [at192, at169, Int.zero_add] using certified
theorem check818 (p : Pattern) : (!walkGuard soko2_2.board support p 192 169 .northWest || decide (bonus 192 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound818 p)
theorem guard819 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 215 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound819 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 215 .southEast = true) : bonus 192 p ≤ bonus 215 p := by
  have certified := compare1086 p (guard819 p guard)
  simpa only [at192, at215, Int.zero_add] using certified
theorem check819 (p : Pattern) : (!walkGuard soko2_2.board support p 192 215 .southEast || decide (bonus 192 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound819 p)
theorem guard820 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 213 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound820 (p : Pattern) (guard : walkGuard soko2_2.board support p 192 213 .southWest = true) : bonus 192 p ≤ bonus 213 p := by
  have certified := compare1086 p (guard820 p guard)
  simpa only [at192, at213, Int.zero_add] using certified
theorem check820 (p : Pattern) : (!walkGuard soko2_2.board support p 192 213 .southWest || decide (bonus 192 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound820 p)
theorem guard821 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 171 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound821 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 171 .north = true) : bonus 193 p ≤ bonus 171 p := by
  have certified := compare1086 p (guard821 p guard)
  simpa only [at193, at171, Int.zero_add] using certified
theorem check821 (p : Pattern) : (!walkGuard soko2_2.board support p 193 171 .north || decide (bonus 193 p ≤ bonus 171 p)) = true :=
  check_of_implication _ _ (bound821 p)
theorem guard822 (p : Pattern) (guard : pushGuard support p 193 171 149 149 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound822 (p : Pattern) (guard : pushGuard support p 193 171 149 149 = true) : bonus 193 p ≤ 1 + Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some 149)) := by
  have certified := compare1087 p (guard822 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 171 (some 149))
  have normalized := agree0 _ _ (change_representative support p 171 (some 149) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check822 (p : Pattern) : (!pushGuard support p 193 171 149 149 || decide (bonus 193 p ≤ 1 + Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some 149)))) = true :=
  check_of_implication _ _ (bound822 p)
theorem guard823 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 215 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound823 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 215 .south = true) : bonus 193 p ≤ bonus 215 p := by
  have certified := compare1086 p (guard823 p guard)
  simpa only [at193, at215, Int.zero_add] using certified
theorem check823 (p : Pattern) : (!walkGuard soko2_2.board support p 193 215 .south || decide (bonus 193 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound823 p)
theorem guard824 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 194 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound824 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 194 .east = true) : bonus 193 p ≤ bonus 194 p := by
  have certified := compare1086 p (guard824 p guard)
  simpa only [at193, at194, Int.zero_add] using certified
theorem check824 (p : Pattern) : (!walkGuard soko2_2.board support p 193 194 .east || decide (bonus 193 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound824 p)
theorem guard825 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 192 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound825 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 192 .west = true) : bonus 193 p ≤ bonus 192 p := by
  have certified := compare1086 p (guard825 p guard)
  simpa only [at193, at192, Int.zero_add] using certified
theorem check825 (p : Pattern) : (!walkGuard soko2_2.board support p 193 192 .west || decide (bonus 193 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound825 p)
theorem guard826 (p : Pattern) (guard : pushGuard support p 193 192 191 191 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound826 (p : Pattern) (guard : pushGuard support p 193 192 191 191 = true) : bonus 193 p ≤ 1 + Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some 191)) := by
  have certified := compare1087 p (guard826 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 192 (some 191))
  have normalized := agree0 _ _ (change_representative support p 192 (some 191) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check826 (p : Pattern) : (!pushGuard support p 193 192 191 191 || decide (bonus 193 p ≤ 1 + Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some 191)))) = true :=
  check_of_implication _ _ (bound826 p)
theorem guard827 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 172 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound827 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 172 .northEast = true) : bonus 193 p ≤ bonus 172 p := by
  have certified := compare1086 p (guard827 p guard)
  simpa only [at193, at172, Int.zero_add] using certified
theorem check827 (p : Pattern) : (!walkGuard soko2_2.board support p 193 172 .northEast || decide (bonus 193 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound827 p)
theorem guard828 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 170 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound828 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 170 .northWest = true) : bonus 193 p ≤ bonus 170 p := by
  have certified := compare1086 p (guard828 p guard)
  simpa only [at193, at170, Int.zero_add] using certified
theorem check828 (p : Pattern) : (!walkGuard soko2_2.board support p 193 170 .northWest || decide (bonus 193 p ≤ bonus 170 p)) = true :=
  check_of_implication _ _ (bound828 p)
theorem guard829 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 216 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound829 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 216 .southEast = true) : bonus 193 p ≤ bonus 216 p := by
  have certified := compare1086 p (guard829 p guard)
  simpa only [at193, at216, Int.zero_add] using certified
theorem check829 (p : Pattern) : (!walkGuard soko2_2.board support p 193 216 .southEast || decide (bonus 193 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound829 p)
theorem guard830 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 214 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound830 (p : Pattern) (guard : walkGuard soko2_2.board support p 193 214 .southWest = true) : bonus 193 p ≤ bonus 214 p := by
  have certified := compare1086 p (guard830 p guard)
  simpa only [at193, at214, Int.zero_add] using certified
theorem check830 (p : Pattern) : (!walkGuard soko2_2.board support p 193 214 .southWest || decide (bonus 193 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound830 p)
theorem guard831 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 172 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound831 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 172 .north = true) : bonus 194 p ≤ bonus 172 p := by
  have certified := compare1086 p (guard831 p guard)
  simpa only [at194, at172, Int.zero_add] using certified
theorem check831 (p : Pattern) : (!walkGuard soko2_2.board support p 194 172 .north || decide (bonus 194 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound831 p)
theorem guard832 (p : Pattern) (guard : pushGuard support p 194 172 150 150 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound832 (p : Pattern) (guard : pushGuard support p 194 172 150 150 = true) : bonus 194 p ≤ 1 + Generated.soko2_2Potential.boulder 150 - Generated.soko2_2Potential.boulder 172 + bonus 172 (change p 172 (some 150)) := by
  have certified := compare1087 p (guard832 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 172 (some 150))
  have normalized := agree0 _ _ (change_representative support p 172 (some 150) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check832 (p : Pattern) : (!pushGuard support p 194 172 150 150 || decide (bonus 194 p ≤ 1 + Generated.soko2_2Potential.boulder 150 - Generated.soko2_2Potential.boulder 172 + bonus 172 (change p 172 (some 150)))) = true :=
  check_of_implication _ _ (bound832 p)
theorem guard833 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 216 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound833 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 216 .south = true) : bonus 194 p ≤ bonus 216 p := by
  have certified := compare1086 p (guard833 p guard)
  simpa only [at194, at216, Int.zero_add] using certified
theorem check833 (p : Pattern) : (!walkGuard soko2_2.board support p 194 216 .south || decide (bonus 194 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound833 p)
theorem guard834 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 193 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound834 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 193 .west = true) : bonus 194 p ≤ bonus 193 p := by
  have certified := compare1086 p (guard834 p guard)
  simpa only [at194, at193, Int.zero_add] using certified
theorem check834 (p : Pattern) : (!walkGuard soko2_2.board support p 194 193 .west || decide (bonus 194 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound834 p)
theorem guard835 (p : Pattern) (guard : pushGuard support p 194 193 192 192 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound835 (p : Pattern) (guard : pushGuard support p 194 193 192 192 = true) : bonus 194 p ≤ 1 + Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some 192)) := by
  have certified := compare1087 p (guard835 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 193 (some 192))
  have normalized := agree0 _ _ (change_representative support p 193 (some 192) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check835 (p : Pattern) : (!pushGuard support p 194 193 192 192 || decide (bonus 194 p ≤ 1 + Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some 192)))) = true :=
  check_of_implication _ _ (bound835 p)
theorem guard836 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 171 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound836 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 171 .northWest = true) : bonus 194 p ≤ bonus 171 p := by
  have certified := compare1086 p (guard836 p guard)
  simpa only [at194, at171, Int.zero_add] using certified
theorem check836 (p : Pattern) : (!walkGuard soko2_2.board support p 194 171 .northWest || decide (bonus 194 p ≤ bonus 171 p)) = true :=
  check_of_implication _ _ (bound836 p)
theorem guard837 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 215 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound837 (p : Pattern) (guard : walkGuard soko2_2.board support p 194 215 .southWest = true) : bonus 194 p ≤ bonus 215 p := by
  have certified := compare1086 p (guard837 p guard)
  simpa only [at194, at215, Int.zero_add] using certified
theorem check837 (p : Pattern) : (!walkGuard soko2_2.board support p 194 215 .southWest || decide (bonus 194 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound837 p)
theorem guard838 (p : Pattern) (guard : walkGuard soko2_2.board support p 199 177 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound838 (p : Pattern) (guard : walkGuard soko2_2.board support p 199 177 .north = true) : bonus 199 p ≤ bonus 177 p := by
  have certified := compare0 p (guard838 p guard)
  simpa only [at199, at177, Int.zero_add] using certified
theorem check838 (p : Pattern) : (!walkGuard soko2_2.board support p 199 177 .north || decide (bonus 199 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound838 p)
theorem guard839 (p : Pattern) (guard : pushGuard support p 199 177 155 155 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound839 (p : Pattern) (guard : pushGuard support p 199 177 155 155 = true) : bonus 199 p ≤ 1 + Generated.soko2_2Potential.boulder 155 - Generated.soko2_2Potential.boulder 177 + bonus 177 (change p 177 (some 155)) := by
  have certified := compare1 p (guard839 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 177 (some 155))
  have normalized := agree267 _ _ (change_representative support p 177 (some 155) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check839 (p : Pattern) : (!pushGuard support p 199 177 155 155 || decide (bonus 199 p ≤ 1 + Generated.soko2_2Potential.boulder 155 - Generated.soko2_2Potential.boulder 177 + bonus 177 (change p 177 (some 155)))) = true :=
  check_of_implication _ _ (bound839 p)
end NetHack.Sokoban22Refined85
