import NetHack.Sokoban22Refined85.ActionBounds036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard888 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 189 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound888 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 189 .northWest = true) : bonus 212 p ≤ bonus 189 p := by
  have certified := compare1086 p (guard888 p guard)
  simpa only [at212, at189, Int.zero_add] using certified
theorem check888 (p : Pattern) : (!walkGuard soko2_2.board support p 212 189 .northWest || decide (bonus 212 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound888 p)
theorem guard889 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 191 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound889 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 191 .north = true) : bonus 213 p ≤ bonus 191 p := by
  have certified := compare1086 p (guard889 p guard)
  simpa only [at213, at191, Int.zero_add] using certified
theorem check889 (p : Pattern) : (!walkGuard soko2_2.board support p 213 191 .north || decide (bonus 213 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound889 p)
theorem guard890 (p : Pattern) (guard : pushGuard support p 213 191 169 169 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound890 (p : Pattern) (guard : pushGuard support p 213 191 169 169 = true) : bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some 169)) := by
  have certified := compare1087 p (guard890 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 191 (some 169))
  have normalized := agree0 _ _ (change_representative support p 191 (some 169) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check890 (p : Pattern) : (!pushGuard support p 213 191 169 169 || decide (bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some 169)))) = true :=
  check_of_implication _ _ (bound890 p)
theorem guard891 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 214 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound891 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 214 .east = true) : bonus 213 p ≤ bonus 214 p := by
  have certified := compare1086 p (guard891 p guard)
  simpa only [at213, at214, Int.zero_add] using certified
theorem check891 (p : Pattern) : (!walkGuard soko2_2.board support p 213 214 .east || decide (bonus 213 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound891 p)
theorem guard892 (p : Pattern) (guard : pushGuard support p 213 214 215 215 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound892 (p : Pattern) (guard : pushGuard support p 213 214 215 215 = true) : bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder 215 - Generated.soko2_2Potential.boulder 214 + bonus 214 (change p 214 (some 215)) := by
  have certified := compare1087 p (guard892 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 214 (some 215))
  have normalized := agree0 _ _ (change_representative support p 214 (some 215) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check892 (p : Pattern) : (!pushGuard support p 213 214 215 215 || decide (bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder 215 - Generated.soko2_2Potential.boulder 214 + bonus 214 (change p 214 (some 215)))) = true :=
  check_of_implication _ _ (bound892 p)
theorem guard893 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 212 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound893 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 212 .west = true) : bonus 213 p ≤ bonus 212 p := by
  have certified := compare1086 p (guard893 p guard)
  simpa only [at213, at212, Int.zero_add] using certified
theorem check893 (p : Pattern) : (!walkGuard soko2_2.board support p 213 212 .west || decide (bonus 213 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound893 p)
theorem guard894 (p : Pattern) (guard : pushGuard support p 213 212 211 211 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound894 (p : Pattern) (guard : pushGuard support p 213 212 211 211 = true) : bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder 211 - Generated.soko2_2Potential.boulder 212 + bonus 212 (change p 212 (some 211)) := by
  have certified := compare1087 p (guard894 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 212 (some 211))
  have normalized := agree0 _ _ (change_representative support p 212 (some 211) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check894 (p : Pattern) : (!pushGuard support p 213 212 211 211 || decide (bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder 211 - Generated.soko2_2Potential.boulder 212 + bonus 212 (change p 212 (some 211)))) = true :=
  check_of_implication _ _ (bound894 p)
theorem guard895 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 192 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound895 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 192 .northEast = true) : bonus 213 p ≤ bonus 192 p := by
  have certified := compare1086 p (guard895 p guard)
  simpa only [at213, at192, Int.zero_add] using certified
theorem check895 (p : Pattern) : (!walkGuard soko2_2.board support p 213 192 .northEast || decide (bonus 213 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound895 p)
theorem guard896 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 190 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound896 (p : Pattern) (guard : walkGuard soko2_2.board support p 213 190 .northWest = true) : bonus 213 p ≤ bonus 190 p := by
  have certified := compare1086 p (guard896 p guard)
  simpa only [at213, at190, Int.zero_add] using certified
theorem check896 (p : Pattern) : (!walkGuard soko2_2.board support p 213 190 .northWest || decide (bonus 213 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound896 p)
theorem guard897 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 192 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound897 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 192 .north = true) : bonus 214 p ≤ bonus 192 p := by
  have certified := compare1086 p (guard897 p guard)
  simpa only [at214, at192, Int.zero_add] using certified
theorem check897 (p : Pattern) : (!walkGuard soko2_2.board support p 214 192 .north || decide (bonus 214 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound897 p)
theorem guard898 (p : Pattern) (guard : pushGuard support p 214 192 170 170 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound898 (p : Pattern) (guard : pushGuard support p 214 192 170 170 = true) : bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some 170)) := by
  have certified := compare1087 p (guard898 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 192 (some 170))
  have normalized := agree0 _ _ (change_representative support p 192 (some 170) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check898 (p : Pattern) : (!pushGuard support p 214 192 170 170 || decide (bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some 170)))) = true :=
  check_of_implication _ _ (bound898 p)
theorem guard899 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 215 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound899 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 215 .east = true) : bonus 214 p ≤ bonus 215 p := by
  have certified := compare1086 p (guard899 p guard)
  simpa only [at214, at215, Int.zero_add] using certified
theorem check899 (p : Pattern) : (!walkGuard soko2_2.board support p 214 215 .east || decide (bonus 214 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound899 p)
theorem guard900 (p : Pattern) (guard : pushGuard support p 214 215 216 216 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound900 (p : Pattern) (guard : pushGuard support p 214 215 216 216 = true) : bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder 216 - Generated.soko2_2Potential.boulder 215 + bonus 215 (change p 215 (some 216)) := by
  have certified := compare1087 p (guard900 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 215 (some 216))
  have normalized := agree0 _ _ (change_representative support p 215 (some 216) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check900 (p : Pattern) : (!pushGuard support p 214 215 216 216 || decide (bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder 216 - Generated.soko2_2Potential.boulder 215 + bonus 215 (change p 215 (some 216)))) = true :=
  check_of_implication _ _ (bound900 p)
theorem guard901 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 213 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound901 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 213 .west = true) : bonus 214 p ≤ bonus 213 p := by
  have certified := compare1086 p (guard901 p guard)
  simpa only [at214, at213, Int.zero_add] using certified
theorem check901 (p : Pattern) : (!walkGuard soko2_2.board support p 214 213 .west || decide (bonus 214 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound901 p)
theorem guard902 (p : Pattern) (guard : pushGuard support p 214 213 212 212 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound902 (p : Pattern) (guard : pushGuard support p 214 213 212 212 = true) : bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder 212 - Generated.soko2_2Potential.boulder 213 + bonus 213 (change p 213 (some 212)) := by
  have certified := compare1087 p (guard902 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 213 (some 212))
  have normalized := agree0 _ _ (change_representative support p 213 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check902 (p : Pattern) : (!pushGuard support p 214 213 212 212 || decide (bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder 212 - Generated.soko2_2Potential.boulder 213 + bonus 213 (change p 213 (some 212)))) = true :=
  check_of_implication _ _ (bound902 p)
theorem guard903 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 193 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound903 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 193 .northEast = true) : bonus 214 p ≤ bonus 193 p := by
  have certified := compare1086 p (guard903 p guard)
  simpa only [at214, at193, Int.zero_add] using certified
theorem check903 (p : Pattern) : (!walkGuard soko2_2.board support p 214 193 .northEast || decide (bonus 214 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound903 p)
theorem guard904 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 191 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound904 (p : Pattern) (guard : walkGuard soko2_2.board support p 214 191 .northWest = true) : bonus 214 p ≤ bonus 191 p := by
  have certified := compare1086 p (guard904 p guard)
  simpa only [at214, at191, Int.zero_add] using certified
theorem check904 (p : Pattern) : (!walkGuard soko2_2.board support p 214 191 .northWest || decide (bonus 214 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound904 p)
theorem guard905 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 193 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound905 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 193 .north = true) : bonus 215 p ≤ bonus 193 p := by
  have certified := compare1086 p (guard905 p guard)
  simpa only [at215, at193, Int.zero_add] using certified
theorem check905 (p : Pattern) : (!walkGuard soko2_2.board support p 215 193 .north || decide (bonus 215 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound905 p)
theorem guard906 (p : Pattern) (guard : pushGuard support p 215 193 171 171 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound906 (p : Pattern) (guard : pushGuard support p 215 193 171 171 = true) : bonus 215 p ≤ 1 + Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some 171)) := by
  have certified := compare1087 p (guard906 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 193 (some 171))
  have normalized := agree0 _ _ (change_representative support p 193 (some 171) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check906 (p : Pattern) : (!pushGuard support p 215 193 171 171 || decide (bonus 215 p ≤ 1 + Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some 171)))) = true :=
  check_of_implication _ _ (bound906 p)
theorem guard907 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 216 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound907 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 216 .east = true) : bonus 215 p ≤ bonus 216 p := by
  have certified := compare1086 p (guard907 p guard)
  simpa only [at215, at216, Int.zero_add] using certified
theorem check907 (p : Pattern) : (!walkGuard soko2_2.board support p 215 216 .east || decide (bonus 215 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound907 p)
theorem guard908 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 214 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound908 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 214 .west = true) : bonus 215 p ≤ bonus 214 p := by
  have certified := compare1086 p (guard908 p guard)
  simpa only [at215, at214, Int.zero_add] using certified
theorem check908 (p : Pattern) : (!walkGuard soko2_2.board support p 215 214 .west || decide (bonus 215 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound908 p)
theorem guard909 (p : Pattern) (guard : pushGuard support p 215 214 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound909 (p : Pattern) (guard : pushGuard support p 215 214 213 213 = true) : bonus 215 p ≤ 1 + Generated.soko2_2Potential.boulder 213 - Generated.soko2_2Potential.boulder 214 + bonus 214 (change p 214 (some 213)) := by
  have certified := compare1087 p (guard909 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 214 (some 213))
  have normalized := agree0 _ _ (change_representative support p 214 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check909 (p : Pattern) : (!pushGuard support p 215 214 213 213 || decide (bonus 215 p ≤ 1 + Generated.soko2_2Potential.boulder 213 - Generated.soko2_2Potential.boulder 214 + bonus 214 (change p 214 (some 213)))) = true :=
  check_of_implication _ _ (bound909 p)
theorem guard910 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 194 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound910 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 194 .northEast = true) : bonus 215 p ≤ bonus 194 p := by
  have certified := compare1086 p (guard910 p guard)
  simpa only [at215, at194, Int.zero_add] using certified
theorem check910 (p : Pattern) : (!walkGuard soko2_2.board support p 215 194 .northEast || decide (bonus 215 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound910 p)
theorem guard911 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 192 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound911 (p : Pattern) (guard : walkGuard soko2_2.board support p 215 192 .northWest = true) : bonus 215 p ≤ bonus 192 p := by
  have certified := compare1086 p (guard911 p guard)
  simpa only [at215, at192, Int.zero_add] using certified
theorem check911 (p : Pattern) : (!walkGuard soko2_2.board support p 215 192 .northWest || decide (bonus 215 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound911 p)
end NetHack.Sokoban22Refined85
