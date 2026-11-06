import NetHack.Sokoban32Refined.ActionBounds036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard888 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 200 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound888 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 200 .west = true) : bonus 201 p ≤ bonus 200 p := by
  have certified := compare103 p (guard888 p guard)
  simpa only [at201, at200, Int.zero_add] using certified
theorem check888 (p : Pattern) : (!walkGuard soko3_2.board support p 201 200 .west || decide (bonus 201 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound888 p)
theorem guard889 (p : Pattern) (guard : pushGuard support p 201 200 199 199 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound889 (p : Pattern) (guard : pushGuard support p 201 200 199 199 = true) : bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder 199 - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some 199)) := by
  have certified := compare37 p (guard889 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 200 (some 199))
  have normalized := agree0 _ _ (change_representative support p 200 (some 199) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check889 (p : Pattern) : (!pushGuard support p 201 200 199 199 || decide (bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder 199 - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some 199)))) = true :=
  check_of_implication _ _ (bound889 p)
theorem guard890 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 176 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound890 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 176 .northEast = true) : bonus 201 p ≤ bonus 176 p := by
  have certified := compare103 p (guard890 p guard)
  simpa only [at201, at176, Int.zero_add] using certified
theorem check890 (p : Pattern) : (!walkGuard soko3_2.board support p 201 176 .northEast || decide (bonus 201 p ≤ bonus 176 p)) = true :=
  check_of_implication _ _ (bound890 p)
theorem guard891 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 174 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound891 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 174 .northWest = true) : bonus 201 p ≤ bonus 174 p := by
  have certified := compare103 p (guard891 p guard)
  simpa only [at201, at174, Int.zero_add] using certified
theorem check891 (p : Pattern) : (!walkGuard soko3_2.board support p 201 174 .northWest || decide (bonus 201 p ≤ bonus 174 p)) = true :=
  check_of_implication _ _ (bound891 p)
theorem guard892 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 228 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound892 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 228 .southEast = true) : bonus 201 p ≤ bonus 228 p := by
  have certified := compare103 p (guard892 p guard)
  simpa only [at201, at228, Int.zero_add] using certified
theorem check892 (p : Pattern) : (!walkGuard soko3_2.board support p 201 228 .southEast || decide (bonus 201 p ≤ bonus 228 p)) = true :=
  check_of_implication _ _ (bound892 p)
theorem guard893 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 226 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound893 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 226 .southWest = true) : bonus 201 p ≤ bonus 226 p := by
  have certified := compare103 p (guard893 p guard)
  simpa only [at201, at226, Int.zero_add] using certified
theorem check893 (p : Pattern) : (!walkGuard soko3_2.board support p 201 226 .southWest || decide (bonus 201 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound893 p)
theorem guard894 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 176 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound894 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 176 .north = true) : bonus 202 p ≤ bonus 176 p := by
  have certified := compare103 p (guard894 p guard)
  simpa only [at202, at176, Int.zero_add] using certified
theorem check894 (p : Pattern) : (!walkGuard soko3_2.board support p 202 176 .north || decide (bonus 202 p ≤ bonus 176 p)) = true :=
  check_of_implication _ _ (bound894 p)
theorem guard895 (p : Pattern) (guard : pushGuard support p 202 176 150 150 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound895 (p : Pattern) (guard : pushGuard support p 202 176 150 150 = true) : bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some 150)) := by
  have certified := compare37 p (guard895 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 176 (some 150))
  have normalized := agree0 _ _ (change_representative support p 176 (some 150) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check895 (p : Pattern) : (!pushGuard support p 202 176 150 150 || decide (bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some 150)))) = true :=
  check_of_implication _ _ (bound895 p)
theorem guard896 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 228 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound896 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 228 .south = true) : bonus 202 p ≤ bonus 228 p := by
  have certified := compare103 p (guard896 p guard)
  simpa only [at202, at228, Int.zero_add] using certified
theorem check896 (p : Pattern) : (!walkGuard soko3_2.board support p 202 228 .south || decide (bonus 202 p ≤ bonus 228 p)) = true :=
  check_of_implication _ _ (bound896 p)
theorem guard897 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 203 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound897 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 203 .east = true) : bonus 202 p ≤ bonus 203 p := by
  have certified := compare103 p (guard897 p guard)
  simpa only [at202, at203, Int.zero_add] using certified
theorem check897 (p : Pattern) : (!walkGuard soko3_2.board support p 202 203 .east || decide (bonus 202 p ≤ bonus 203 p)) = true :=
  check_of_implication _ _ (bound897 p)
theorem guard898 (p : Pattern) (guard : pushGuard support p 202 203 204 204 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound898 (p : Pattern) (guard : pushGuard support p 202 203 204 204 = true) : bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some 204)) := by
  have certified := compare37 p (guard898 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 203 (some 204))
  have normalized := agree0 _ _ (change_representative support p 203 (some 204) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check898 (p : Pattern) : (!pushGuard support p 202 203 204 204 || decide (bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some 204)))) = true :=
  check_of_implication _ _ (bound898 p)
theorem guard899 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 201 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound899 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 201 .west = true) : bonus 202 p ≤ bonus 201 p := by
  have certified := compare103 p (guard899 p guard)
  simpa only [at202, at201, Int.zero_add] using certified
theorem check899 (p : Pattern) : (!walkGuard soko3_2.board support p 202 201 .west || decide (bonus 202 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound899 p)
theorem guard900 (p : Pattern) (guard : pushGuard support p 202 201 200 200 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound900 (p : Pattern) (guard : pushGuard support p 202 201 200 200 = true) : bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some 200)) := by
  have certified := compare37 p (guard900 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 201 (some 200))
  have normalized := agree0 _ _ (change_representative support p 201 (some 200) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check900 (p : Pattern) : (!pushGuard support p 202 201 200 200 || decide (bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some 200)))) = true :=
  check_of_implication _ _ (bound900 p)
theorem guard901 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 177 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound901 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 177 .northEast = true) : bonus 202 p ≤ bonus 177 p := by
  have certified := compare103 p (guard901 p guard)
  simpa only [at202, at177, Int.zero_add] using certified
theorem check901 (p : Pattern) : (!walkGuard soko3_2.board support p 202 177 .northEast || decide (bonus 202 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound901 p)
theorem guard902 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 175 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound902 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 175 .northWest = true) : bonus 202 p ≤ bonus 175 p := by
  have certified := compare103 p (guard902 p guard)
  simpa only [at202, at175, Int.zero_add] using certified
theorem check902 (p : Pattern) : (!walkGuard soko3_2.board support p 202 175 .northWest || decide (bonus 202 p ≤ bonus 175 p)) = true :=
  check_of_implication _ _ (bound902 p)
theorem guard903 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 229 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound903 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 229 .southEast = true) : bonus 202 p ≤ bonus 229 p := by
  have certified := compare103 p (guard903 p guard)
  simpa only [at202, at229, Int.zero_add] using certified
theorem check903 (p : Pattern) : (!walkGuard soko3_2.board support p 202 229 .southEast || decide (bonus 202 p ≤ bonus 229 p)) = true :=
  check_of_implication _ _ (bound903 p)
theorem guard904 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 227 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound904 (p : Pattern) (guard : walkGuard soko3_2.board support p 202 227 .southWest = true) : bonus 202 p ≤ bonus 227 p := by
  have certified := compare103 p (guard904 p guard)
  simpa only [at202, at227, Int.zero_add] using certified
theorem check904 (p : Pattern) : (!walkGuard soko3_2.board support p 202 227 .southWest || decide (bonus 202 p ≤ bonus 227 p)) = true :=
  check_of_implication _ _ (bound904 p)
theorem guard905 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 177 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound905 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 177 .north = true) : bonus 203 p ≤ bonus 177 p := by
  have certified := compare103 p (guard905 p guard)
  simpa only [at203, at177, Int.zero_add] using certified
theorem check905 (p : Pattern) : (!walkGuard soko3_2.board support p 203 177 .north || decide (bonus 203 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound905 p)
theorem guard906 (p : Pattern) (guard : pushGuard support p 203 177 151 151 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound906 (p : Pattern) (guard : pushGuard support p 203 177 151 151 = true) : bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some 151)) := by
  have certified := compare37 p (guard906 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 177 (some 151))
  have normalized := agree0 _ _ (change_representative support p 177 (some 151) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check906 (p : Pattern) : (!pushGuard support p 203 177 151 151 || decide (bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some 151)))) = true :=
  check_of_implication _ _ (bound906 p)
theorem guard907 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 229 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound907 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 229 .south = true) : bonus 203 p ≤ bonus 229 p := by
  have certified := compare103 p (guard907 p guard)
  simpa only [at203, at229, Int.zero_add] using certified
theorem check907 (p : Pattern) : (!walkGuard soko3_2.board support p 203 229 .south || decide (bonus 203 p ≤ bonus 229 p)) = true :=
  check_of_implication _ _ (bound907 p)
theorem guard908 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 204 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound908 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 204 .east = true) : bonus 203 p ≤ bonus 204 p := by
  have certified := compare103 p (guard908 p guard)
  simpa only [at203, at204, Int.zero_add] using certified
theorem check908 (p : Pattern) : (!walkGuard soko3_2.board support p 203 204 .east || decide (bonus 203 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound908 p)
theorem guard909 (p : Pattern) (guard : pushGuard support p 203 204 205 205 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound909 (p : Pattern) (guard : pushGuard support p 203 204 205 205 = true) : bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder 205 - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some 205)) := by
  have certified := compare37 p (guard909 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 204 (some 205))
  have normalized := agree0 _ _ (change_representative support p 204 (some 205) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check909 (p : Pattern) : (!pushGuard support p 203 204 205 205 || decide (bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder 205 - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some 205)))) = true :=
  check_of_implication _ _ (bound909 p)
theorem guard910 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 202 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound910 (p : Pattern) (guard : walkGuard soko3_2.board support p 203 202 .west = true) : bonus 203 p ≤ bonus 202 p := by
  have certified := compare103 p (guard910 p guard)
  simpa only [at203, at202, Int.zero_add] using certified
theorem check910 (p : Pattern) : (!walkGuard soko3_2.board support p 203 202 .west || decide (bonus 203 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound910 p)
theorem guard911 (p : Pattern) (guard : pushGuard support p 203 202 201 201 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound911 (p : Pattern) (guard : pushGuard support p 203 202 201 201 = true) : bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some 201)) := by
  have certified := compare37 p (guard911 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 202 (some 201))
  have normalized := agree0 _ _ (change_representative support p 202 (some 201) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check911 (p : Pattern) : (!pushGuard support p 203 202 201 201 || decide (bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some 201)))) = true :=
  check_of_implication _ _ (bound911 p)
end NetHack.Sokoban32Refined
