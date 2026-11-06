import NetHack.Sokoban32Refined.ActionBounds043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1056 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 230 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1056 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 230 .west = true) : bonus 231 p ≤ bonus 230 p := by
  have certified := compare103 p (guard1056 p guard)
  simpa only [at231, at230, Int.zero_add] using certified
theorem check1056 (p : Pattern) : (!walkGuard soko3_2.board support p 231 230 .west || decide (bonus 231 p ≤ bonus 230 p)) = true :=
  check_of_implication _ _ (bound1056 p)
theorem guard1057 (p : Pattern) (guard : pushGuard support p 231 230 229 229 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1057 (p : Pattern) (guard : pushGuard support p 231 230 229 229 = true) : bonus 231 p ≤ 1 + Generated.soko3_2Potential.boulder 229 - Generated.soko3_2Potential.boulder 230 + bonus 230 (change p 230 (some 229)) := by
  have certified := compare37 p (guard1057 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 230 (some 229))
  have normalized := agree0 _ _ (change_representative support p 230 (some 229) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1057 (p : Pattern) : (!pushGuard support p 231 230 229 229 || decide (bonus 231 p ≤ 1 + Generated.soko3_2Potential.boulder 229 - Generated.soko3_2Potential.boulder 230 + bonus 230 (change p 230 (some 229)))) = true :=
  check_of_implication _ _ (bound1057 p)
theorem guard1058 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 206 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1058 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 206 .northEast = true) : bonus 231 p ≤ bonus 206 p := by
  have certified := compare103 p (guard1058 p guard)
  simpa only [at231, at206, Int.zero_add] using certified
theorem check1058 (p : Pattern) : (!walkGuard soko3_2.board support p 231 206 .northEast || decide (bonus 231 p ≤ bonus 206 p)) = true :=
  check_of_implication _ _ (bound1058 p)
theorem guard1059 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 204 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1059 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 204 .northWest = true) : bonus 231 p ≤ bonus 204 p := by
  have certified := compare103 p (guard1059 p guard)
  simpa only [at231, at204, Int.zero_add] using certified
theorem check1059 (p : Pattern) : (!walkGuard soko3_2.board support p 231 204 .northWest || decide (bonus 231 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound1059 p)
theorem guard1060 (p : Pattern) (guard : walkGuard soko3_2.board support p 232 206 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1060 (p : Pattern) (guard : walkGuard soko3_2.board support p 232 206 .north = true) : bonus 232 p ≤ bonus 206 p := by
  have certified := compare103 p (guard1060 p guard)
  simpa only [at232, at206, Int.zero_add] using certified
theorem check1060 (p : Pattern) : (!walkGuard soko3_2.board support p 232 206 .north || decide (bonus 232 p ≤ bonus 206 p)) = true :=
  check_of_implication _ _ (bound1060 p)
theorem guard1061 (p : Pattern) (guard : pushGuard support p 232 206 180 180 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1061 (p : Pattern) (guard : pushGuard support p 232 206 180 180 = true) : bonus 232 p ≤ 1 + Generated.soko3_2Potential.boulder 180 - Generated.soko3_2Potential.boulder 206 + bonus 206 (change p 206 (some 180)) := by
  have certified := compare37 p (guard1061 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 206 (some 180))
  have normalized := agree0 _ _ (change_representative support p 206 (some 180) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1061 (p : Pattern) : (!pushGuard support p 232 206 180 180 || decide (bonus 232 p ≤ 1 + Generated.soko3_2Potential.boulder 180 - Generated.soko3_2Potential.boulder 206 + bonus 206 (change p 206 (some 180)))) = true :=
  check_of_implication _ _ (bound1061 p)
theorem guard1062 (p : Pattern) (guard : walkGuard soko3_2.board support p 232 231 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1062 (p : Pattern) (guard : walkGuard soko3_2.board support p 232 231 .west = true) : bonus 232 p ≤ bonus 231 p := by
  have certified := compare103 p (guard1062 p guard)
  simpa only [at232, at231, Int.zero_add] using certified
theorem check1062 (p : Pattern) : (!walkGuard soko3_2.board support p 232 231 .west || decide (bonus 232 p ≤ bonus 231 p)) = true :=
  check_of_implication _ _ (bound1062 p)
theorem guard1063 (p : Pattern) (guard : pushGuard support p 232 231 230 230 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1063 (p : Pattern) (guard : pushGuard support p 232 231 230 230 = true) : bonus 232 p ≤ 1 + Generated.soko3_2Potential.boulder 230 - Generated.soko3_2Potential.boulder 231 + bonus 231 (change p 231 (some 230)) := by
  have certified := compare37 p (guard1063 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 231 (some 230))
  have normalized := agree0 _ _ (change_representative support p 231 (some 230) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1063 (p : Pattern) : (!pushGuard support p 232 231 230 230 || decide (bonus 232 p ≤ 1 + Generated.soko3_2Potential.boulder 230 - Generated.soko3_2Potential.boulder 231 + bonus 231 (change p 231 (some 230)))) = true :=
  check_of_implication _ _ (bound1063 p)
theorem guard1064 (p : Pattern) (guard : walkGuard soko3_2.board support p 232 205 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1064 (p : Pattern) (guard : walkGuard soko3_2.board support p 232 205 .northWest = true) : bonus 232 p ≤ bonus 205 p := by
  have certified := compare103 p (guard1064 p guard)
  simpa only [at232, at205, Int.zero_add] using certified
theorem check1064 (p : Pattern) : (!walkGuard soko3_2.board support p 232 205 .northWest || decide (bonus 232 p ≤ bonus 205 p)) = true :=
  check_of_implication _ _ (bound1064 p)
theorem guard1065 (p : Pattern) (guard : walkGuard soko3_2.board support p 235 209 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1065 (p : Pattern) (guard : walkGuard soko3_2.board support p 235 209 .north = true) : bonus 235 p ≤ bonus 209 p := by
  have certified := compare0 p (guard1065 p guard)
  simpa only [at235, at209, Int.zero_add] using certified
theorem check1065 (p : Pattern) : (!walkGuard soko3_2.board support p 235 209 .north || decide (bonus 235 p ≤ bonus 209 p)) = true :=
  check_of_implication _ _ (bound1065 p)
theorem guard1066 (p : Pattern) (guard : pushGuard support p 235 209 183 183 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1066 (p : Pattern) (guard : pushGuard support p 235 209 183 183 = true) : bonus 235 p ≤ 1 + Generated.soko3_2Potential.boulder 183 - Generated.soko3_2Potential.boulder 209 + bonus 209 (change p 209 (some 183)) := by
  have certified := compare104 p (guard1066 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 209 (some 183))
  have normalized := agree134 _ _ (change_representative support p 209 (some 183) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1066 (p : Pattern) : (!pushGuard support p 235 209 183 183 || decide (bonus 235 p ≤ 1 + Generated.soko3_2Potential.boulder 183 - Generated.soko3_2Potential.boulder 209 + bonus 209 (change p 209 (some 183)))) = true :=
  check_of_implication _ _ (bound1066 p)
theorem guard1067 (p : Pattern) (guard : walkGuard soko3_2.board support p 235 261 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1067 (p : Pattern) (guard : walkGuard soko3_2.board support p 235 261 .south = true) : bonus 235 p ≤ bonus 261 p := by
  have certified := compare0 p (guard1067 p guard)
  simpa only [at235, at261, Int.zero_add] using certified
theorem check1067 (p : Pattern) : (!walkGuard soko3_2.board support p 235 261 .south || decide (bonus 235 p ≤ bonus 261 p)) = true :=
  check_of_implication _ _ (bound1067 p)
theorem guard1068 (p : Pattern) (guard : pushGuard support p 235 261 287 287 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1068 (p : Pattern) (guard : pushGuard support p 235 261 287 287 = true) : bonus 235 p ≤ 1 + Generated.soko3_2Potential.boulder 287 - Generated.soko3_2Potential.boulder 261 + bonus 261 (change p 261 (some 287)) := by
  have certified := compare104 p (guard1068 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 261 (some 287))
  have normalized := agree134 _ _ (change_representative support p 261 (some 287) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1068 (p : Pattern) : (!pushGuard support p 235 261 287 287 || decide (bonus 235 p ≤ 1 + Generated.soko3_2Potential.boulder 287 - Generated.soko3_2Potential.boulder 261 + bonus 261 (change p 261 (some 287)))) = true :=
  check_of_implication _ _ (bound1068 p)
theorem guard1069 (p : Pattern) (guard : walkGuard soko3_2.board support p 235 210 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1069 (p : Pattern) (guard : walkGuard soko3_2.board support p 235 210 .northEast = true) : bonus 235 p ≤ bonus 210 p := by
  have certified := compare0 p (guard1069 p guard)
  simpa only [at235, at210, Int.zero_add] using certified
theorem check1069 (p : Pattern) : (!walkGuard soko3_2.board support p 235 210 .northEast || decide (bonus 235 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound1069 p)
theorem guard1070 (p : Pattern) (guard : walkGuard soko3_2.board support p 235 262 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1070 (p : Pattern) (guard : walkGuard soko3_2.board support p 235 262 .southEast = true) : bonus 235 p ≤ bonus 262 p := by
  have certified := compare0 p (guard1070 p guard)
  simpa only [at235, at262, Int.zero_add] using certified
theorem check1070 (p : Pattern) : (!walkGuard soko3_2.board support p 235 262 .southEast || decide (bonus 235 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound1070 p)
theorem guard1071 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 213 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1071 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 213 .north = true) : bonus 239 p ≤ bonus 213 p := by
  have certified := compare0 p (guard1071 p guard)
  simpa only [at239, at213, Int.zero_add] using certified
theorem check1071 (p : Pattern) : (!walkGuard soko3_2.board support p 239 213 .north || decide (bonus 239 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound1071 p)
theorem guard1072 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 265 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1072 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 265 .south = true) : bonus 239 p ≤ bonus 265 p := by
  have certified := compare0 p (guard1072 p guard)
  simpa only [at239, at265, Int.zero_add] using certified
theorem check1072 (p : Pattern) : (!walkGuard soko3_2.board support p 239 265 .south || decide (bonus 239 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound1072 p)
theorem guard1073 (p : Pattern) (guard : pushGuard support p 239 265 291 291 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1073 (p : Pattern) (guard : pushGuard support p 239 265 291 291 = true) : bonus 239 p ≤ 1 + Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.boulder 265 + bonus 265 (change p 265 (some 291)) := by
  have certified := compare0 p (guard1073 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 265 (some 291))
  have normalized := agree134 _ _ (change_representative support p 265 (some 291) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1073 (p : Pattern) : (!pushGuard support p 239 265 291 291 || decide (bonus 239 p ≤ 1 + Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.boulder 265 + bonus 265 (change p 265 (some 291)))) = true :=
  check_of_implication _ _ (bound1073 p)
theorem guard1074 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 214 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1074 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 214 .northEast = true) : bonus 239 p ≤ bonus 214 p := by
  have certified := compare0 p (guard1074 p guard)
  simpa only [at239, at214, Int.zero_add] using certified
theorem check1074 (p : Pattern) : (!walkGuard soko3_2.board support p 239 214 .northEast || decide (bonus 239 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound1074 p)
theorem guard1075 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 212 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1075 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 212 .northWest = true) : bonus 239 p ≤ bonus 212 p := by
  have certified := compare0 p (guard1075 p guard)
  simpa only [at239, at212, Int.zero_add] using certified
theorem check1075 (p : Pattern) : (!walkGuard soko3_2.board support p 239 212 .northWest || decide (bonus 239 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound1075 p)
theorem guard1076 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 266 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1076 (p : Pattern) (guard : walkGuard soko3_2.board support p 239 266 .southEast = true) : bonus 239 p ≤ bonus 266 p := by
  have certified := compare0 p (guard1076 p guard)
  simpa only [at239, at266, Int.zero_add] using certified
theorem check1076 (p : Pattern) : (!walkGuard soko3_2.board support p 239 266 .southEast || decide (bonus 239 p ≤ bonus 266 p)) = true :=
  check_of_implication _ _ (bound1076 p)
theorem guard1077 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 215 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1077 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 215 .north = true) : bonus 241 p ≤ bonus 215 p := by
  have certified := compare0 p (guard1077 p guard)
  simpa only [at241, at215, Int.zero_add] using certified
theorem check1077 (p : Pattern) : (!walkGuard soko3_2.board support p 241 215 .north || decide (bonus 241 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound1077 p)
theorem guard1078 (p : Pattern) (guard : pushGuard support p 241 215 189 189 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1078 (p : Pattern) (guard : pushGuard support p 241 215 189 189 = true) : bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder 189 - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some 189)) := by
  have certified := compare4301 p (guard1078 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 215 (some 189))
  have normalized := agree134 _ _ (change_representative support p 215 (some 189) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1078 (p : Pattern) : (!pushGuard support p 241 215 189 189 || decide (bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder 189 - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some 189)))) = true :=
  check_of_implication _ _ (bound1078 p)
theorem guard1079 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 267 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1079 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 267 .south = true) : bonus 241 p ≤ bonus 267 p := by
  have certified := compare0 p (guard1079 p guard)
  simpa only [at241, at267, Int.zero_add] using certified
theorem check1079 (p : Pattern) : (!walkGuard soko3_2.board support p 241 267 .south || decide (bonus 241 p ≤ bonus 267 p)) = true :=
  check_of_implication _ _ (bound1079 p)
end NetHack.Sokoban32Refined
