import NetHack.Sokoban32Refined.ActionBounds046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1128 (p : Pattern) (guard : walkGuard soko3_2.board support p 263 289 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1128 (p : Pattern) (guard : walkGuard soko3_2.board support p 263 289 .south = true) : bonus 263 p ≤ bonus 289 p := by
  have certified := compare0 p (guard1128 p guard)
  simpa only [at263, at289, Int.zero_add] using certified
theorem check1128 (p : Pattern) : (!walkGuard soko3_2.board support p 263 289 .south || decide (bonus 263 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound1128 p)
theorem guard1129 (p : Pattern) (guard : walkGuard soko3_2.board support p 263 262 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1129 (p : Pattern) (guard : walkGuard soko3_2.board support p 263 262 .west = true) : bonus 263 p ≤ bonus 262 p := by
  have certified := compare0 p (guard1129 p guard)
  simpa only [at263, at262, Int.zero_add] using certified
theorem check1129 (p : Pattern) : (!walkGuard soko3_2.board support p 263 262 .west || decide (bonus 263 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound1129 p)
theorem guard1130 (p : Pattern) (guard : pushGuard support p 263 262 261 261 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1130 (p : Pattern) (guard : pushGuard support p 263 262 261 261 = true) : bonus 263 p ≤ 1 + Generated.soko3_2Potential.boulder 261 - Generated.soko3_2Potential.boulder 262 + bonus 262 (change p 262 (some 261)) := by
  have certified := compare104 p (guard1130 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 262 (some 261))
  have normalized := agree134 _ _ (change_representative support p 262 (some 261) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1130 (p : Pattern) : (!pushGuard support p 263 262 261 261 || decide (bonus 263 p ≤ 1 + Generated.soko3_2Potential.boulder 261 - Generated.soko3_2Potential.boulder 262 + bonus 262 (change p 262 (some 261)))) = true :=
  check_of_implication _ _ (bound1130 p)
theorem guard1131 (p : Pattern) (guard : walkGuard soko3_2.board support p 263 290 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1131 (p : Pattern) (guard : walkGuard soko3_2.board support p 263 290 .southEast = true) : bonus 263 p ≤ bonus 290 p := by
  have certified := compare0 p (guard1131 p guard)
  simpa only [at263, at290, Int.zero_add] using certified
theorem check1131 (p : Pattern) : (!walkGuard soko3_2.board support p 263 290 .southEast || decide (bonus 263 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound1131 p)
theorem guard1132 (p : Pattern) (guard : walkGuard soko3_2.board support p 263 288 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1132 (p : Pattern) (guard : walkGuard soko3_2.board support p 263 288 .southWest = true) : bonus 263 p ≤ bonus 288 p := by
  have certified := compare0 p (guard1132 p guard)
  simpa only [at263, at288, Int.zero_add] using certified
theorem check1132 (p : Pattern) : (!walkGuard soko3_2.board support p 263 288 .southWest || decide (bonus 263 p ≤ bonus 288 p)) = true :=
  check_of_implication _ _ (bound1132 p)
theorem guard1133 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 239 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1133 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 239 .north = true) : bonus 265 p ≤ bonus 239 p := by
  have certified := compare0 p (guard1133 p guard)
  simpa only [at265, at239, Int.zero_add] using certified
theorem check1133 (p : Pattern) : (!walkGuard soko3_2.board support p 265 239 .north || decide (bonus 265 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound1133 p)
theorem guard1134 (p : Pattern) (guard : pushGuard support p 265 239 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1134 (p : Pattern) (guard : pushGuard support p 265 239 213 213 = true) : bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder 213 - Generated.soko3_2Potential.boulder 239 + bonus 239 (change p 239 (some 213)) := by
  have certified := compare4301 p (guard1134 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 239 (some 213))
  have normalized := agree134 _ _ (change_representative support p 239 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1134 (p : Pattern) : (!pushGuard support p 265 239 213 213 || decide (bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder 213 - Generated.soko3_2Potential.boulder 239 + bonus 239 (change p 239 (some 213)))) = true :=
  check_of_implication _ _ (bound1134 p)
theorem guard1135 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 291 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1135 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 291 .south = true) : bonus 265 p ≤ bonus 291 p := by
  have certified := compare0 p (guard1135 p guard)
  simpa only [at265, at291, Int.zero_add] using certified
theorem check1135 (p : Pattern) : (!walkGuard soko3_2.board support p 265 291 .south || decide (bonus 265 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound1135 p)
theorem guard1136 (p : Pattern) (guard : pushGuard support p 265 291 317 317 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1136 (p : Pattern) (guard : pushGuard support p 265 291 317 317 = true) : bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder 317 - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some 317)) := by
  have certified := compare9365 p (guard1136 p guard)
  change d134 p ≤ (10 : Int) + d134 (change p 291 (some 317))
  have normalized := agree134 _ _ (change_representative support p 291 (some 317) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (10 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1136 (p : Pattern) : (!pushGuard support p 265 291 317 317 || decide (bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder 317 - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some 317)))) = true :=
  check_of_implication _ _ (bound1136 p)
theorem guard1137 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 266 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1137 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 266 .east = true) : bonus 265 p ≤ bonus 266 p := by
  have certified := compare0 p (guard1137 p guard)
  simpa only [at265, at266, Int.zero_add] using certified
theorem check1137 (p : Pattern) : (!walkGuard soko3_2.board support p 265 266 .east || decide (bonus 265 p ≤ bonus 266 p)) = true :=
  check_of_implication _ _ (bound1137 p)
theorem guard1138 (p : Pattern) (guard : pushGuard support p 265 266 267 267 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1138 (p : Pattern) (guard : pushGuard support p 265 266 267 267 = true) : bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder 267 - Generated.soko3_2Potential.boulder 266 + bonus 266 (change p 266 (some 267)) := by
  have certified := compare0 p (guard1138 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 266 (some 267))
  have normalized := agree134 _ _ (change_representative support p 266 (some 267) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1138 (p : Pattern) : (!pushGuard support p 265 266 267 267 || decide (bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder 267 - Generated.soko3_2Potential.boulder 266 + bonus 266 (change p 266 (some 267)))) = true :=
  check_of_implication _ _ (bound1138 p)
theorem guard1139 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 292 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1139 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 292 .southEast = true) : bonus 265 p ≤ bonus 292 p := by
  have certified := compare0 p (guard1139 p guard)
  simpa only [at265, at292, Int.zero_add] using certified
theorem check1139 (p : Pattern) : (!walkGuard soko3_2.board support p 265 292 .southEast || decide (bonus 265 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound1139 p)
theorem guard1140 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 290 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1140 (p : Pattern) (guard : walkGuard soko3_2.board support p 265 290 .southWest = true) : bonus 265 p ≤ bonus 290 p := by
  have certified := compare0 p (guard1140 p guard)
  simpa only [at265, at290, Int.zero_add] using certified
theorem check1140 (p : Pattern) : (!walkGuard soko3_2.board support p 265 290 .southWest || decide (bonus 265 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound1140 p)
theorem guard1141 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 292 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1141 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 292 .south = true) : bonus 266 p ≤ bonus 292 p := by
  have certified := compare0 p (guard1141 p guard)
  simpa only [at266, at292, Int.zero_add] using certified
theorem check1141 (p : Pattern) : (!walkGuard soko3_2.board support p 266 292 .south || decide (bonus 266 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound1141 p)
theorem guard1142 (p : Pattern) (guard : pushGuard support p 266 292 318 318 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1142 (p : Pattern) (guard : pushGuard support p 266 292 318 318 = true) : bonus 266 p ≤ 1 + Generated.soko3_2Potential.boulder 318 - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some 318)) := by
  have certified := compare9366 p (guard1142 p guard)
  change d134 p ≤ (11 : Int) + d134 (change p 292 (some 318))
  have normalized := agree134 _ _ (change_representative support p 292 (some 318) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (11 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1142 (p : Pattern) : (!pushGuard support p 266 292 318 318 || decide (bonus 266 p ≤ 1 + Generated.soko3_2Potential.boulder 318 - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some 318)))) = true :=
  check_of_implication _ _ (bound1142 p)
theorem guard1143 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 267 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1143 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 267 .east = true) : bonus 266 p ≤ bonus 267 p := by
  have certified := compare0 p (guard1143 p guard)
  simpa only [at266, at267, Int.zero_add] using certified
theorem check1143 (p : Pattern) : (!walkGuard soko3_2.board support p 266 267 .east || decide (bonus 266 p ≤ bonus 267 p)) = true :=
  check_of_implication _ _ (bound1143 p)
theorem guard1144 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 265 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1144 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 265 .west = true) : bonus 266 p ≤ bonus 265 p := by
  have certified := compare0 p (guard1144 p guard)
  simpa only [at266, at265, Int.zero_add] using certified
theorem check1144 (p : Pattern) : (!walkGuard soko3_2.board support p 266 265 .west || decide (bonus 266 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound1144 p)
theorem guard1145 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 241 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1145 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 241 .northEast = true) : bonus 266 p ≤ bonus 241 p := by
  have certified := compare0 p (guard1145 p guard)
  simpa only [at266, at241, Int.zero_add] using certified
theorem check1145 (p : Pattern) : (!walkGuard soko3_2.board support p 266 241 .northEast || decide (bonus 266 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound1145 p)
theorem guard1146 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 239 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1146 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 239 .northWest = true) : bonus 266 p ≤ bonus 239 p := by
  have certified := compare0 p (guard1146 p guard)
  simpa only [at266, at239, Int.zero_add] using certified
theorem check1146 (p : Pattern) : (!walkGuard soko3_2.board support p 266 239 .northWest || decide (bonus 266 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound1146 p)
theorem guard1147 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 293 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1147 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 293 .southEast = true) : bonus 266 p ≤ bonus 293 p := by
  have certified := compare0 p (guard1147 p guard)
  simpa only [at266, at293, Int.zero_add] using certified
theorem check1147 (p : Pattern) : (!walkGuard soko3_2.board support p 266 293 .southEast || decide (bonus 266 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound1147 p)
theorem guard1148 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 291 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1148 (p : Pattern) (guard : walkGuard soko3_2.board support p 266 291 .southWest = true) : bonus 266 p ≤ bonus 291 p := by
  have certified := compare0 p (guard1148 p guard)
  simpa only [at266, at291, Int.zero_add] using certified
theorem check1148 (p : Pattern) : (!walkGuard soko3_2.board support p 266 291 .southWest || decide (bonus 266 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound1148 p)
theorem guard1149 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 241 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1149 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 241 .north = true) : bonus 267 p ≤ bonus 241 p := by
  have certified := compare0 p (guard1149 p guard)
  simpa only [at267, at241, Int.zero_add] using certified
theorem check1149 (p : Pattern) : (!walkGuard soko3_2.board support p 267 241 .north || decide (bonus 267 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound1149 p)
theorem guard1150 (p : Pattern) (guard : pushGuard support p 267 241 215 215 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1150 (p : Pattern) (guard : pushGuard support p 267 241 215 215 = true) : bonus 267 p ≤ 1 + Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.boulder 241 + bonus 241 (change p 241 (some 215)) := by
  have certified := compare4301 p (guard1150 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 241 (some 215))
  have normalized := agree134 _ _ (change_representative support p 241 (some 215) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1150 (p : Pattern) : (!pushGuard support p 267 241 215 215 || decide (bonus 267 p ≤ 1 + Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.boulder 241 + bonus 241 (change p 241 (some 215)))) = true :=
  check_of_implication _ _ (bound1150 p)
theorem guard1151 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 293 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1151 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 293 .south = true) : bonus 267 p ≤ bonus 293 p := by
  have certified := compare0 p (guard1151 p guard)
  simpa only [at267, at293, Int.zero_add] using certified
theorem check1151 (p : Pattern) : (!walkGuard soko3_2.board support p 267 293 .south || decide (bonus 267 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound1151 p)
end NetHack.Sokoban32Refined
