import NetHack.Sokoban32Refined.ActionBounds047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1152 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 266 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1152 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 266 .west = true) : bonus 267 p ≤ bonus 266 p := by
  have certified := compare0 p (guard1152 p guard)
  simpa only [at267, at266, Int.zero_add] using certified
theorem check1152 (p : Pattern) : (!walkGuard soko3_2.board support p 267 266 .west || decide (bonus 267 p ≤ bonus 266 p)) = true :=
  check_of_implication _ _ (bound1152 p)
theorem guard1153 (p : Pattern) (guard : pushGuard support p 267 266 265 265 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1153 (p : Pattern) (guard : pushGuard support p 267 266 265 265 = true) : bonus 267 p ≤ 1 + Generated.soko3_2Potential.boulder 265 - Generated.soko3_2Potential.boulder 266 + bonus 266 (change p 266 (some 265)) := by
  have certified := compare4301 p (guard1153 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 266 (some 265))
  have normalized := agree134 _ _ (change_representative support p 266 (some 265) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1153 (p : Pattern) : (!pushGuard support p 267 266 265 265 || decide (bonus 267 p ≤ 1 + Generated.soko3_2Potential.boulder 265 - Generated.soko3_2Potential.boulder 266 + bonus 266 (change p 266 (some 265)))) = true :=
  check_of_implication _ _ (bound1153 p)
theorem guard1154 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 242 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1154 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 242 .northEast = true) : bonus 267 p ≤ bonus 242 p := by
  have certified := compare0 p (guard1154 p guard)
  simpa only [at267, at242, Int.zero_add] using certified
theorem check1154 (p : Pattern) : (!walkGuard soko3_2.board support p 267 242 .northEast || decide (bonus 267 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound1154 p)
theorem guard1155 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 294 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1155 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 294 .southEast = true) : bonus 267 p ≤ bonus 294 p := by
  have certified := compare0 p (guard1155 p guard)
  simpa only [at267, at294, Int.zero_add] using certified
theorem check1155 (p : Pattern) : (!walkGuard soko3_2.board support p 267 294 .southEast || decide (bonus 267 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound1155 p)
theorem guard1156 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 292 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1156 (p : Pattern) (guard : walkGuard soko3_2.board support p 267 292 .southWest = true) : bonus 267 p ≤ bonus 292 p := by
  have certified := compare0 p (guard1156 p guard)
  simpa only [at267, at292, Int.zero_add] using certified
theorem check1156 (p : Pattern) : (!walkGuard soko3_2.board support p 267 292 .southWest || decide (bonus 267 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound1156 p)
theorem guard1157 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 243 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1157 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 243 .north = true) : bonus 269 p ≤ bonus 243 p := by
  have certified := compare0 p (guard1157 p guard)
  simpa only [at269, at243, Int.zero_add] using certified
theorem check1157 (p : Pattern) : (!walkGuard soko3_2.board support p 269 243 .north || decide (bonus 269 p ≤ bonus 243 p)) = true :=
  check_of_implication _ _ (bound1157 p)
theorem guard1158 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 295 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1158 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 295 .south = true) : bonus 269 p ≤ bonus 295 p := by
  have certified := compare0 p (guard1158 p guard)
  simpa only [at269, at295, Int.zero_add] using certified
theorem check1158 (p : Pattern) : (!walkGuard soko3_2.board support p 269 295 .south || decide (bonus 269 p ≤ bonus 295 p)) = true :=
  check_of_implication _ _ (bound1158 p)
theorem guard1159 (p : Pattern) (guard : pushGuard support p 269 295 321 321 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1159 (p : Pattern) (guard : pushGuard support p 269 295 321 321 = true) : bonus 269 p ≤ 1 + Generated.soko3_2Potential.boulder 321 - Generated.soko3_2Potential.boulder 295 + bonus 295 (change p 295 (some 321)) := by
  have certified := compare9367 p (guard1159 p guard)
  change d134 p ≤ (14 : Int) + d134 (change p 295 (some 321))
  have normalized := agree134 _ _ (change_representative support p 295 (some 321) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (14 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1159 (p : Pattern) : (!pushGuard support p 269 295 321 321 || decide (bonus 269 p ≤ 1 + Generated.soko3_2Potential.boulder 321 - Generated.soko3_2Potential.boulder 295 + bonus 295 (change p 295 (some 321)))) = true :=
  check_of_implication _ _ (bound1159 p)
theorem guard1160 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 270 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1160 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 270 .east = true) : bonus 269 p ≤ bonus 270 p := by
  have certified := compare0 p (guard1160 p guard)
  simpa only [at269, at270, Int.zero_add] using certified
theorem check1160 (p : Pattern) : (!walkGuard soko3_2.board support p 269 270 .east || decide (bonus 269 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound1160 p)
theorem guard1161 (p : Pattern) (guard : pushGuard support p 269 270 271 284 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1161 (p : Pattern) (guard : pushGuard support p 269 270 271 284 = true) : bonus 269 p ≤ 1 + Generated.soko3_2Potential.boulder 284 - Generated.soko3_2Potential.boulder 270 + bonus 270 (change p 270 (some 284)) := by
  have certified := compare9368 p (guard1161 p guard)
  change d134 p ≤ (18 : Int) + d134 (change p 270 (some 284))
  have normalized := agree134 _ _ (change_representative support p 270 (some 284) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (18 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1161 (p : Pattern) : (!pushGuard support p 269 270 271 284 || decide (bonus 269 p ≤ 1 + Generated.soko3_2Potential.boulder 284 - Generated.soko3_2Potential.boulder 270 + bonus 270 (change p 270 (some 284)))) = true :=
  check_of_implication _ _ (bound1161 p)
theorem guard1162 (p : Pattern) (guard : pushGuard support p 269 270 271 272 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1162 (p : Pattern) (guard : pushGuard support p 269 270 271 272 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 272 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1162 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1162 (p : Pattern) : (!pushGuard support p 269 270 271 272 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 272 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1162 p)
theorem guard1163 (p : Pattern) (guard : pushGuard support p 269 270 271 273 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1163 (p : Pattern) (guard : pushGuard support p 269 270 271 273 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 273 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1163 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1163 (p : Pattern) : (!pushGuard support p 269 270 271 273 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 273 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1163 p)
theorem guard1164 (p : Pattern) (guard : pushGuard support p 269 270 271 274 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1164 (p : Pattern) (guard : pushGuard support p 269 270 271 274 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 274 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1164 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1164 (p : Pattern) : (!pushGuard support p 269 270 271 274 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 274 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1164 p)
theorem guard1165 (p : Pattern) (guard : pushGuard support p 269 270 271 275 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1165 (p : Pattern) (guard : pushGuard support p 269 270 271 275 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 275 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1165 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1165 (p : Pattern) : (!pushGuard support p 269 270 271 275 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 275 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1165 p)
theorem guard1166 (p : Pattern) (guard : pushGuard support p 269 270 271 276 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1166 (p : Pattern) (guard : pushGuard support p 269 270 271 276 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 276 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1166 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1166 (p : Pattern) : (!pushGuard support p 269 270 271 276 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 276 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1166 p)
theorem guard1167 (p : Pattern) (guard : pushGuard support p 269 270 271 277 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1167 (p : Pattern) (guard : pushGuard support p 269 270 271 277 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 277 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1167 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1167 (p : Pattern) : (!pushGuard support p 269 270 271 277 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 277 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1167 p)
theorem guard1168 (p : Pattern) (guard : pushGuard support p 269 270 271 278 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1168 (p : Pattern) (guard : pushGuard support p 269 270 271 278 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 278 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1168 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1168 (p : Pattern) : (!pushGuard support p 269 270 271 278 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 278 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1168 p)
theorem guard1169 (p : Pattern) (guard : pushGuard support p 269 270 271 279 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1169 (p : Pattern) (guard : pushGuard support p 269 270 271 279 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 279 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1169 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1169 (p : Pattern) : (!pushGuard support p 269 270 271 279 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 279 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1169 p)
theorem guard1170 (p : Pattern) (guard : pushGuard support p 269 270 271 280 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1170 (p : Pattern) (guard : pushGuard support p 269 270 271 280 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 280 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1170 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1170 (p : Pattern) : (!pushGuard support p 269 270 271 280 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 280 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1170 p)
theorem guard1171 (p : Pattern) (guard : pushGuard support p 269 270 271 281 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1171 (p : Pattern) (guard : pushGuard support p 269 270 271 281 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 281 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1171 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1171 (p : Pattern) : (!pushGuard support p 269 270 271 281 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 281 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1171 p)
theorem guard1172 (p : Pattern) (guard : pushGuard support p 269 270 271 282 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1172 (p : Pattern) (guard : pushGuard support p 269 270 271 282 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 282 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1172 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1172 (p : Pattern) : (!pushGuard support p 269 270 271 282 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 282 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1172 p)
theorem guard1173 (p : Pattern) (guard : pushGuard support p 269 270 271 283 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1173 (p : Pattern) (guard : pushGuard support p 269 270 271 283 = true) : bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 283 + bonus 270 (change p 270 none) := by
  have certified := compare0 p (guard1173 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 270 none)
  have normalized := agree134 _ _ (change_representative support p 270 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1173 (p : Pattern) : (!pushGuard support p 269 270 271 283 || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole 283 + bonus 270 (change p 270 none))) = true :=
  check_of_implication _ _ (bound1173 p)
theorem guard1174 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 244 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1174 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 244 .northEast = true) : bonus 269 p ≤ bonus 244 p := by
  have certified := compare0 p (guard1174 p guard)
  simpa only [at269, at244, Int.zero_add] using certified
theorem check1174 (p : Pattern) : (!walkGuard soko3_2.board support p 269 244 .northEast || decide (bonus 269 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound1174 p)
theorem guard1175 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 242 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1175 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 242 .northWest = true) : bonus 269 p ≤ bonus 242 p := by
  have certified := compare0 p (guard1175 p guard)
  simpa only [at269, at242, Int.zero_add] using certified
theorem check1175 (p : Pattern) : (!walkGuard soko3_2.board support p 269 242 .northWest || decide (bonus 269 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound1175 p)
end NetHack.Sokoban32Refined
