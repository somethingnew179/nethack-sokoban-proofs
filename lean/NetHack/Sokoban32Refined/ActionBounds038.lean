import NetHack.Sokoban32Refined.ActionBounds037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard912 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 178 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound912 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 178 .northEast = true) : bonus 203 p ≤ bonus 178 p := by
  have certified := compare103 p (guard912 p guard)
  simpa only [at203, at178, Int.zero_add] using certified
theorem check912 (p : Pattern) : (!walkGuard soko3_2.board support p 203 178 .northEast || decide (bonus 203 p ≤ bonus 178 p)) = true :=
  check_of_implication _ _ (bound912 p)
theorem guard913 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 176 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound913 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 176 .northWest = true) : bonus 203 p ≤ bonus 176 p := by
  have certified := compare103 p (guard913 p guard)
  simpa only [at203, at176, Int.zero_add] using certified
theorem check913 (p : Pattern) : (!walkGuard soko3_2.board support p 203 176 .northWest || decide (bonus 203 p ≤ bonus 176 p)) = true :=
  check_of_implication _ _ (bound913 p)
theorem guard914 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 230 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound914 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 230 .southEast = true) : bonus 203 p ≤ bonus 230 p := by
  have certified := compare103 p (guard914 p guard)
  simpa only [at203, at230, Int.zero_add] using certified
theorem check914 (p : Pattern) : (!walkGuard soko3_2.board support p 203 230 .southEast || decide (bonus 203 p ≤ bonus 230 p)) = true :=
  check_of_implication _ _ (bound914 p)
theorem guard915 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 228 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound915 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 228 .southWest = true) : bonus 203 p ≤ bonus 228 p := by
  have certified := compare103 p (guard915 p guard)
  simpa only [at203, at228, Int.zero_add] using certified
theorem check915 (p : Pattern) : (!walkGuard soko3_2.board support p 203 228 .southWest || decide (bonus 203 p ≤ bonus 228 p)) = true :=
  check_of_implication _ _ (bound915 p)
theorem guard916 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 178 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound916 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 178 .north = true) : bonus 204 p ≤ bonus 178 p := by
  have certified := compare103 p (guard916 p guard)
  simpa only [at204, at178, Int.zero_add] using certified
theorem check916 (p : Pattern) : (!walkGuard soko3_2.board support p 204 178 .north || decide (bonus 204 p ≤ bonus 178 p)) = true :=
  check_of_implication _ _ (bound916 p)
theorem guard917 (p : Pattern) (guard : pushGuard support p 204 178 152 152 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound917 (p : Pattern) (guard : pushGuard support p 204 178 152 152 = true) : bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some 152)) := by
  have certified := compare37 p (guard917 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 178 (some 152))
  have normalized := agree0 _ _ (change_representative support p 178 (some 152) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check917 (p : Pattern) : (!pushGuard support p 204 178 152 152 || decide (bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some 152)))) = true :=
  check_of_implication _ _ (bound917 p)
theorem guard918 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 230 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound918 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 230 .south = true) : bonus 204 p ≤ bonus 230 p := by
  have certified := compare103 p (guard918 p guard)
  simpa only [at204, at230, Int.zero_add] using certified
theorem check918 (p : Pattern) : (!walkGuard soko3_2.board support p 204 230 .south || decide (bonus 204 p ≤ bonus 230 p)) = true :=
  check_of_implication _ _ (bound918 p)
theorem guard919 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 205 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound919 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 205 .east = true) : bonus 204 p ≤ bonus 205 p := by
  have certified := compare103 p (guard919 p guard)
  simpa only [at204, at205, Int.zero_add] using certified
theorem check919 (p : Pattern) : (!walkGuard soko3_2.board support p 204 205 .east || decide (bonus 204 p ≤ bonus 205 p)) = true :=
  check_of_implication _ _ (bound919 p)
theorem guard920 (p : Pattern) (guard : pushGuard support p 204 205 206 206 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound920 (p : Pattern) (guard : pushGuard support p 204 205 206 206 = true) : bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder 206 - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some 206)) := by
  have certified := compare37 p (guard920 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 205 (some 206))
  have normalized := agree0 _ _ (change_representative support p 205 (some 206) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check920 (p : Pattern) : (!pushGuard support p 204 205 206 206 || decide (bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder 206 - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some 206)))) = true :=
  check_of_implication _ _ (bound920 p)
theorem guard921 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 203 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound921 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 203 .west = true) : bonus 204 p ≤ bonus 203 p := by
  have certified := compare103 p (guard921 p guard)
  simpa only [at204, at203, Int.zero_add] using certified
theorem check921 (p : Pattern) : (!walkGuard soko3_2.board support p 204 203 .west || decide (bonus 204 p ≤ bonus 203 p)) = true :=
  check_of_implication _ _ (bound921 p)
theorem guard922 (p : Pattern) (guard : pushGuard support p 204 203 202 202 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound922 (p : Pattern) (guard : pushGuard support p 204 203 202 202 = true) : bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some 202)) := by
  have certified := compare37 p (guard922 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 203 (some 202))
  have normalized := agree0 _ _ (change_representative support p 203 (some 202) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check922 (p : Pattern) : (!pushGuard support p 204 203 202 202 || decide (bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some 202)))) = true :=
  check_of_implication _ _ (bound922 p)
theorem guard923 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 179 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound923 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 179 .northEast = true) : bonus 204 p ≤ bonus 179 p := by
  have certified := compare103 p (guard923 p guard)
  simpa only [at204, at179, Int.zero_add] using certified
theorem check923 (p : Pattern) : (!walkGuard soko3_2.board support p 204 179 .northEast || decide (bonus 204 p ≤ bonus 179 p)) = true :=
  check_of_implication _ _ (bound923 p)
theorem guard924 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 177 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound924 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 177 .northWest = true) : bonus 204 p ≤ bonus 177 p := by
  have certified := compare103 p (guard924 p guard)
  simpa only [at204, at177, Int.zero_add] using certified
theorem check924 (p : Pattern) : (!walkGuard soko3_2.board support p 204 177 .northWest || decide (bonus 204 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound924 p)
theorem guard925 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 231 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound925 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 231 .southEast = true) : bonus 204 p ≤ bonus 231 p := by
  have certified := compare103 p (guard925 p guard)
  simpa only [at204, at231, Int.zero_add] using certified
theorem check925 (p : Pattern) : (!walkGuard soko3_2.board support p 204 231 .southEast || decide (bonus 204 p ≤ bonus 231 p)) = true :=
  check_of_implication _ _ (bound925 p)
theorem guard926 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 229 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound926 (p : Pattern) (guard : walkGuard soko3_2.board support p 204 229 .southWest = true) : bonus 204 p ≤ bonus 229 p := by
  have certified := compare103 p (guard926 p guard)
  simpa only [at204, at229, Int.zero_add] using certified
theorem check926 (p : Pattern) : (!walkGuard soko3_2.board support p 204 229 .southWest || decide (bonus 204 p ≤ bonus 229 p)) = true :=
  check_of_implication _ _ (bound926 p)
theorem guard927 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 179 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound927 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 179 .north = true) : bonus 205 p ≤ bonus 179 p := by
  have certified := compare103 p (guard927 p guard)
  simpa only [at205, at179, Int.zero_add] using certified
theorem check927 (p : Pattern) : (!walkGuard soko3_2.board support p 205 179 .north || decide (bonus 205 p ≤ bonus 179 p)) = true :=
  check_of_implication _ _ (bound927 p)
theorem guard928 (p : Pattern) (guard : pushGuard support p 205 179 153 153 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound928 (p : Pattern) (guard : pushGuard support p 205 179 153 153 = true) : bonus 205 p ≤ 1 + Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some 153)) := by
  have certified := compare37 p (guard928 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 179 (some 153))
  have normalized := agree0 _ _ (change_representative support p 179 (some 153) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check928 (p : Pattern) : (!pushGuard support p 205 179 153 153 || decide (bonus 205 p ≤ 1 + Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some 153)))) = true :=
  check_of_implication _ _ (bound928 p)
theorem guard929 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 231 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound929 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 231 .south = true) : bonus 205 p ≤ bonus 231 p := by
  have certified := compare103 p (guard929 p guard)
  simpa only [at205, at231, Int.zero_add] using certified
theorem check929 (p : Pattern) : (!walkGuard soko3_2.board support p 205 231 .south || decide (bonus 205 p ≤ bonus 231 p)) = true :=
  check_of_implication _ _ (bound929 p)
theorem guard930 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 206 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound930 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 206 .east = true) : bonus 205 p ≤ bonus 206 p := by
  have certified := compare103 p (guard930 p guard)
  simpa only [at205, at206, Int.zero_add] using certified
theorem check930 (p : Pattern) : (!walkGuard soko3_2.board support p 205 206 .east || decide (bonus 205 p ≤ bonus 206 p)) = true :=
  check_of_implication _ _ (bound930 p)
theorem guard931 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 204 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound931 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 204 .west = true) : bonus 205 p ≤ bonus 204 p := by
  have certified := compare103 p (guard931 p guard)
  simpa only [at205, at204, Int.zero_add] using certified
theorem check931 (p : Pattern) : (!walkGuard soko3_2.board support p 205 204 .west || decide (bonus 205 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound931 p)
theorem guard932 (p : Pattern) (guard : pushGuard support p 205 204 203 203 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound932 (p : Pattern) (guard : pushGuard support p 205 204 203 203 = true) : bonus 205 p ≤ 1 + Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some 203)) := by
  have certified := compare37 p (guard932 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 204 (some 203))
  have normalized := agree0 _ _ (change_representative support p 204 (some 203) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check932 (p : Pattern) : (!pushGuard support p 205 204 203 203 || decide (bonus 205 p ≤ 1 + Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some 203)))) = true :=
  check_of_implication _ _ (bound932 p)
theorem guard933 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 180 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound933 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 180 .northEast = true) : bonus 205 p ≤ bonus 180 p := by
  have certified := compare103 p (guard933 p guard)
  simpa only [at205, at180, Int.zero_add] using certified
theorem check933 (p : Pattern) : (!walkGuard soko3_2.board support p 205 180 .northEast || decide (bonus 205 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound933 p)
theorem guard934 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 178 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound934 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 178 .northWest = true) : bonus 205 p ≤ bonus 178 p := by
  have certified := compare103 p (guard934 p guard)
  simpa only [at205, at178, Int.zero_add] using certified
theorem check934 (p : Pattern) : (!walkGuard soko3_2.board support p 205 178 .northWest || decide (bonus 205 p ≤ bonus 178 p)) = true :=
  check_of_implication _ _ (bound934 p)
theorem guard935 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 232 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound935 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 232 .southEast = true) : bonus 205 p ≤ bonus 232 p := by
  have certified := compare103 p (guard935 p guard)
  simpa only [at205, at232, Int.zero_add] using certified
theorem check935 (p : Pattern) : (!walkGuard soko3_2.board support p 205 232 .southEast || decide (bonus 205 p ≤ bonus 232 p)) = true :=
  check_of_implication _ _ (bound935 p)
end NetHack.Sokoban32Refined
