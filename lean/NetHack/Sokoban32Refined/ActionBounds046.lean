import NetHack.Sokoban32Refined.ActionBounds045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1104 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 270 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1104 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 270 .south = true) : bonus 244 p ≤ bonus 270 p := by
  have certified := compare0 p (guard1104 p guard)
  simpa only [at244, at270, Int.zero_add] using certified
theorem check1104 (p : Pattern) : (!walkGuard soko3_2.board support p 244 270 .south || decide (bonus 244 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound1104 p)
theorem guard1105 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 245 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1105 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 245 .east = true) : bonus 244 p ≤ bonus 245 p := by
  have certified := compare0 p (guard1105 p guard)
  simpa only [at244, at245, Int.zero_add] using certified
theorem check1105 (p : Pattern) : (!walkGuard soko3_2.board support p 244 245 .east || decide (bonus 244 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound1105 p)
theorem guard1106 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 243 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1106 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 243 .west = true) : bonus 244 p ≤ bonus 243 p := by
  have certified := compare0 p (guard1106 p guard)
  simpa only [at244, at243, Int.zero_add] using certified
theorem check1106 (p : Pattern) : (!walkGuard soko3_2.board support p 244 243 .west || decide (bonus 244 p ≤ bonus 243 p)) = true :=
  check_of_implication _ _ (bound1106 p)
theorem guard1107 (p : Pattern) (guard : pushGuard support p 244 243 242 242 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1107 (p : Pattern) (guard : pushGuard support p 244 243 242 242 = true) : bonus 244 p ≤ 1 + Generated.soko3_2Potential.boulder 242 - Generated.soko3_2Potential.boulder 243 + bonus 243 (change p 243 (some 242)) := by
  have certified := compare4301 p (guard1107 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 243 (some 242))
  have normalized := agree134 _ _ (change_representative support p 243 (some 242) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1107 (p : Pattern) : (!pushGuard support p 244 243 242 242 || decide (bonus 244 p ≤ 1 + Generated.soko3_2Potential.boulder 242 - Generated.soko3_2Potential.boulder 243 + bonus 243 (change p 243 (some 242)))) = true :=
  check_of_implication _ _ (bound1107 p)
theorem guard1108 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 271 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1108 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 271 .southEast = true) : bonus 244 p ≤ bonus 271 p := by
  have certified := compare0 p (guard1108 p guard)
  simpa only [at244, at271, Int.zero_add] using certified
theorem check1108 (p : Pattern) : (!walkGuard soko3_2.board support p 244 271 .southEast || decide (bonus 244 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound1108 p)
theorem guard1109 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 269 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1109 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 269 .southWest = true) : bonus 244 p ≤ bonus 269 p := by
  have certified := compare0 p (guard1109 p guard)
  simpa only [at244, at269, Int.zero_add] using certified
theorem check1109 (p : Pattern) : (!walkGuard soko3_2.board support p 244 269 .southWest || decide (bonus 244 p ≤ bonus 269 p)) = true :=
  check_of_implication _ _ (bound1109 p)
theorem guard1110 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 271 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1110 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 271 .south = true) : bonus 245 p ≤ bonus 271 p := by
  have certified := compare0 p (guard1110 p guard)
  simpa only [at245, at271, Int.zero_add] using certified
theorem check1110 (p : Pattern) : (!walkGuard soko3_2.board support p 245 271 .south || decide (bonus 245 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound1110 p)
theorem guard1111 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 244 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1111 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 244 .west = true) : bonus 245 p ≤ bonus 244 p := by
  have certified := compare0 p (guard1111 p guard)
  simpa only [at245, at244, Int.zero_add] using certified
theorem check1111 (p : Pattern) : (!walkGuard soko3_2.board support p 245 244 .west || decide (bonus 245 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound1111 p)
theorem guard1112 (p : Pattern) (guard : pushGuard support p 245 244 243 243 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1112 (p : Pattern) (guard : pushGuard support p 245 244 243 243 = true) : bonus 245 p ≤ 1 + Generated.soko3_2Potential.boulder 243 - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some 243)) := by
  have certified := compare4301 p (guard1112 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 244 (some 243))
  have normalized := agree134 _ _ (change_representative support p 244 (some 243) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1112 (p : Pattern) : (!pushGuard support p 245 244 243 243 || decide (bonus 245 p ≤ 1 + Generated.soko3_2Potential.boulder 243 - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some 243)))) = true :=
  check_of_implication _ _ (bound1112 p)
theorem guard1113 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 218 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1113 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 218 .northWest = true) : bonus 245 p ≤ bonus 218 p := by
  have certified := compare0 p (guard1113 p guard)
  simpa only [at245, at218, Int.zero_add] using certified
theorem check1113 (p : Pattern) : (!walkGuard soko3_2.board support p 245 218 .northWest || decide (bonus 245 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound1113 p)
theorem guard1114 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 272 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1114 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 272 .southEast = true) : bonus 245 p ≤ bonus 272 p := by
  have certified := compare0 p (guard1114 p guard)
  simpa only [at245, at272, Int.zero_add] using certified
theorem check1114 (p : Pattern) : (!walkGuard soko3_2.board support p 245 272 .southEast || decide (bonus 245 p ≤ bonus 272 p)) = true :=
  check_of_implication _ _ (bound1114 p)
theorem guard1115 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 270 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1115 (p : Pattern) (guard : walkGuard soko3_2.board support p 245 270 .southWest = true) : bonus 245 p ≤ bonus 270 p := by
  have certified := compare0 p (guard1115 p guard)
  simpa only [at245, at270, Int.zero_add] using certified
theorem check1115 (p : Pattern) : (!walkGuard soko3_2.board support p 245 270 .southWest || decide (bonus 245 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound1115 p)
theorem guard1116 (p : Pattern) (guard : walkGuard soko3_2.board support p 261 235 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1116 (p : Pattern) (guard : walkGuard soko3_2.board support p 261 235 .north = true) : bonus 261 p ≤ bonus 235 p := by
  have certified := compare0 p (guard1116 p guard)
  simpa only [at261, at235, Int.zero_add] using certified
theorem check1116 (p : Pattern) : (!walkGuard soko3_2.board support p 261 235 .north || decide (bonus 261 p ≤ bonus 235 p)) = true :=
  check_of_implication _ _ (bound1116 p)
theorem guard1117 (p : Pattern) (guard : pushGuard support p 261 235 209 209 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1117 (p : Pattern) (guard : pushGuard support p 261 235 209 209 = true) : bonus 261 p ≤ 1 + Generated.soko3_2Potential.boulder 209 - Generated.soko3_2Potential.boulder 235 + bonus 235 (change p 235 (some 209)) := by
  have certified := compare104 p (guard1117 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 235 (some 209))
  have normalized := agree134 _ _ (change_representative support p 235 (some 209) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1117 (p : Pattern) : (!pushGuard support p 261 235 209 209 || decide (bonus 261 p ≤ 1 + Generated.soko3_2Potential.boulder 209 - Generated.soko3_2Potential.boulder 235 + bonus 235 (change p 235 (some 209)))) = true :=
  check_of_implication _ _ (bound1117 p)
theorem guard1118 (p : Pattern) (guard : walkGuard soko3_2.board support p 261 287 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1118 (p : Pattern) (guard : walkGuard soko3_2.board support p 261 287 .south = true) : bonus 261 p ≤ bonus 287 p := by
  have certified := compare0 p (guard1118 p guard)
  simpa only [at261, at287, Int.zero_add] using certified
theorem check1118 (p : Pattern) : (!walkGuard soko3_2.board support p 261 287 .south || decide (bonus 261 p ≤ bonus 287 p)) = true :=
  check_of_implication _ _ (bound1118 p)
theorem guard1119 (p : Pattern) (guard : walkGuard soko3_2.board support p 261 262 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1119 (p : Pattern) (guard : walkGuard soko3_2.board support p 261 262 .east = true) : bonus 261 p ≤ bonus 262 p := by
  have certified := compare0 p (guard1119 p guard)
  simpa only [at261, at262, Int.zero_add] using certified
theorem check1119 (p : Pattern) : (!walkGuard soko3_2.board support p 261 262 .east || decide (bonus 261 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound1119 p)
theorem guard1120 (p : Pattern) (guard : pushGuard support p 261 262 263 263 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1120 (p : Pattern) (guard : pushGuard support p 261 262 263 263 = true) : bonus 261 p ≤ 1 + Generated.soko3_2Potential.boulder 263 - Generated.soko3_2Potential.boulder 262 + bonus 262 (change p 262 (some 263)) := by
  have certified := compare104 p (guard1120 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 262 (some 263))
  have normalized := agree134 _ _ (change_representative support p 262 (some 263) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1120 (p : Pattern) : (!pushGuard support p 261 262 263 263 || decide (bonus 261 p ≤ 1 + Generated.soko3_2Potential.boulder 263 - Generated.soko3_2Potential.boulder 262 + bonus 262 (change p 262 (some 263)))) = true :=
  check_of_implication _ _ (bound1120 p)
theorem guard1121 (p : Pattern) (guard : walkGuard soko3_2.board support p 261 288 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1121 (p : Pattern) (guard : walkGuard soko3_2.board support p 261 288 .southEast = true) : bonus 261 p ≤ bonus 288 p := by
  have certified := compare0 p (guard1121 p guard)
  simpa only [at261, at288, Int.zero_add] using certified
theorem check1121 (p : Pattern) : (!walkGuard soko3_2.board support p 261 288 .southEast || decide (bonus 261 p ≤ bonus 288 p)) = true :=
  check_of_implication _ _ (bound1121 p)
theorem guard1122 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 288 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1122 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 288 .south = true) : bonus 262 p ≤ bonus 288 p := by
  have certified := compare0 p (guard1122 p guard)
  simpa only [at262, at288, Int.zero_add] using certified
theorem check1122 (p : Pattern) : (!walkGuard soko3_2.board support p 262 288 .south || decide (bonus 262 p ≤ bonus 288 p)) = true :=
  check_of_implication _ _ (bound1122 p)
theorem guard1123 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 263 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1123 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 263 .east = true) : bonus 262 p ≤ bonus 263 p := by
  have certified := compare0 p (guard1123 p guard)
  simpa only [at262, at263, Int.zero_add] using certified
theorem check1123 (p : Pattern) : (!walkGuard soko3_2.board support p 262 263 .east || decide (bonus 262 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound1123 p)
theorem guard1124 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 261 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1124 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 261 .west = true) : bonus 262 p ≤ bonus 261 p := by
  have certified := compare0 p (guard1124 p guard)
  simpa only [at262, at261, Int.zero_add] using certified
theorem check1124 (p : Pattern) : (!walkGuard soko3_2.board support p 262 261 .west || decide (bonus 262 p ≤ bonus 261 p)) = true :=
  check_of_implication _ _ (bound1124 p)
theorem guard1125 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 235 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1125 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 235 .northWest = true) : bonus 262 p ≤ bonus 235 p := by
  have certified := compare0 p (guard1125 p guard)
  simpa only [at262, at235, Int.zero_add] using certified
theorem check1125 (p : Pattern) : (!walkGuard soko3_2.board support p 262 235 .northWest || decide (bonus 262 p ≤ bonus 235 p)) = true :=
  check_of_implication _ _ (bound1125 p)
theorem guard1126 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 289 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1126 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 289 .southEast = true) : bonus 262 p ≤ bonus 289 p := by
  have certified := compare0 p (guard1126 p guard)
  simpa only [at262, at289, Int.zero_add] using certified
theorem check1126 (p : Pattern) : (!walkGuard soko3_2.board support p 262 289 .southEast || decide (bonus 262 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound1126 p)
theorem guard1127 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 287 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1127 (p : Pattern) (guard : walkGuard soko3_2.board support p 262 287 .southWest = true) : bonus 262 p ≤ bonus 287 p := by
  have certified := compare0 p (guard1127 p guard)
  simpa only [at262, at287, Int.zero_add] using certified
theorem check1127 (p : Pattern) : (!walkGuard soko3_2.board support p 262 287 .southWest || decide (bonus 262 p ≤ bonus 287 p)) = true :=
  check_of_implication _ _ (bound1127 p)
end NetHack.Sokoban32Refined
