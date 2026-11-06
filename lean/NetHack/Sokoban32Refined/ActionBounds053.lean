import NetHack.Sokoban32Refined.ActionBounds052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1272 (p : Pattern) (guard : pushGuard support p 288 289 290 290 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1272 (p : Pattern) (guard : pushGuard support p 288 289 290 290 = true) : bonus 288 p ≤ 1 + Generated.soko3_2Potential.boulder 290 - Generated.soko3_2Potential.boulder 289 + bonus 289 (change p 289 (some 290)) := by
  have certified := compare0 p (guard1272 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 289 (some 290))
  have normalized := agree134 _ _ (change_representative support p 289 (some 290) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1272 (p : Pattern) : (!pushGuard support p 288 289 290 290 || decide (bonus 288 p ≤ 1 + Generated.soko3_2Potential.boulder 290 - Generated.soko3_2Potential.boulder 289 + bonus 289 (change p 289 (some 290)))) = true :=
  check_of_implication _ _ (bound1272 p)
theorem guard1273 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 287 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1273 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 287 .west = true) : bonus 288 p ≤ bonus 287 p := by
  have certified := compare0 p (guard1273 p guard)
  simpa only [at288, at287, Int.zero_add] using certified
theorem check1273 (p : Pattern) : (!walkGuard soko3_2.board support p 288 287 .west || decide (bonus 288 p ≤ bonus 287 p)) = true :=
  check_of_implication _ _ (bound1273 p)
theorem guard1274 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 263 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1274 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 263 .northEast = true) : bonus 288 p ≤ bonus 263 p := by
  have certified := compare0 p (guard1274 p guard)
  simpa only [at288, at263, Int.zero_add] using certified
theorem check1274 (p : Pattern) : (!walkGuard soko3_2.board support p 288 263 .northEast || decide (bonus 288 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound1274 p)
theorem guard1275 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 261 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1275 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 261 .northWest = true) : bonus 288 p ≤ bonus 261 p := by
  have certified := compare0 p (guard1275 p guard)
  simpa only [at288, at261, Int.zero_add] using certified
theorem check1275 (p : Pattern) : (!walkGuard soko3_2.board support p 288 261 .northWest || decide (bonus 288 p ≤ bonus 261 p)) = true :=
  check_of_implication _ _ (bound1275 p)
theorem guard1276 (p : Pattern) (guard : walkGuard soko3_2.board support p 289 263 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1276 (p : Pattern) (guard : walkGuard soko3_2.board support p 289 263 .north = true) : bonus 289 p ≤ bonus 263 p := by
  have certified := compare0 p (guard1276 p guard)
  simpa only [at289, at263, Int.zero_add] using certified
theorem check1276 (p : Pattern) : (!walkGuard soko3_2.board support p 289 263 .north || decide (bonus 289 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound1276 p)
theorem guard1277 (p : Pattern) (guard : walkGuard soko3_2.board support p 289 290 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1277 (p : Pattern) (guard : walkGuard soko3_2.board support p 289 290 .east = true) : bonus 289 p ≤ bonus 290 p := by
  have certified := compare0 p (guard1277 p guard)
  simpa only [at289, at290, Int.zero_add] using certified
theorem check1277 (p : Pattern) : (!walkGuard soko3_2.board support p 289 290 .east || decide (bonus 289 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound1277 p)
theorem guard1278 (p : Pattern) (guard : pushGuard support p 289 290 291 291 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1278 (p : Pattern) (guard : pushGuard support p 289 290 291 291 = true) : bonus 289 p ≤ 1 + Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.boulder 290 + bonus 290 (change p 290 (some 291)) := by
  have certified := compare0 p (guard1278 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 290 (some 291))
  have normalized := agree134 _ _ (change_representative support p 290 (some 291) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1278 (p : Pattern) : (!pushGuard support p 289 290 291 291 || decide (bonus 289 p ≤ 1 + Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.boulder 290 + bonus 290 (change p 290 (some 291)))) = true :=
  check_of_implication _ _ (bound1278 p)
theorem guard1279 (p : Pattern) (guard : walkGuard soko3_2.board support p 289 288 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1279 (p : Pattern) (guard : walkGuard soko3_2.board support p 289 288 .west = true) : bonus 289 p ≤ bonus 288 p := by
  have certified := compare0 p (guard1279 p guard)
  simpa only [at289, at288, Int.zero_add] using certified
theorem check1279 (p : Pattern) : (!walkGuard soko3_2.board support p 289 288 .west || decide (bonus 289 p ≤ bonus 288 p)) = true :=
  check_of_implication _ _ (bound1279 p)
theorem guard1280 (p : Pattern) (guard : pushGuard support p 289 288 287 287 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1280 (p : Pattern) (guard : pushGuard support p 289 288 287 287 = true) : bonus 289 p ≤ 1 + Generated.soko3_2Potential.boulder 287 - Generated.soko3_2Potential.boulder 288 + bonus 288 (change p 288 (some 287)) := by
  have certified := compare9370 p (guard1280 p guard)
  change d134 p ≤ (7 : Int) + d134 (change p 288 (some 287))
  have normalized := agree134 _ _ (change_representative support p 288 (some 287) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (7 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1280 (p : Pattern) : (!pushGuard support p 289 288 287 287 || decide (bonus 289 p ≤ 1 + Generated.soko3_2Potential.boulder 287 - Generated.soko3_2Potential.boulder 288 + bonus 288 (change p 288 (some 287)))) = true :=
  check_of_implication _ _ (bound1280 p)
theorem guard1281 (p : Pattern) (guard : walkGuard soko3_2.board support p 289 262 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1281 (p : Pattern) (guard : walkGuard soko3_2.board support p 289 262 .northWest = true) : bonus 289 p ≤ bonus 262 p := by
  have certified := compare0 p (guard1281 p guard)
  simpa only [at289, at262, Int.zero_add] using certified
theorem check1281 (p : Pattern) : (!walkGuard soko3_2.board support p 289 262 .northWest || decide (bonus 289 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound1281 p)
theorem guard1282 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 291 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1282 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 291 .east = true) : bonus 290 p ≤ bonus 291 p := by
  have certified := compare0 p (guard1282 p guard)
  simpa only [at290, at291, Int.zero_add] using certified
theorem check1282 (p : Pattern) : (!walkGuard soko3_2.board support p 290 291 .east || decide (bonus 290 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound1282 p)
theorem guard1283 (p : Pattern) (guard : pushGuard support p 290 291 292 292 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1283 (p : Pattern) (guard : pushGuard support p 290 291 292 292 = true) : bonus 290 p ≤ 1 + Generated.soko3_2Potential.boulder 292 - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some 292)) := by
  have certified := compare0 p (guard1283 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 291 (some 292))
  have normalized := agree134 _ _ (change_representative support p 291 (some 292) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1283 (p : Pattern) : (!pushGuard support p 290 291 292 292 || decide (bonus 290 p ≤ 1 + Generated.soko3_2Potential.boulder 292 - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some 292)))) = true :=
  check_of_implication _ _ (bound1283 p)
theorem guard1284 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 289 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1284 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 289 .west = true) : bonus 290 p ≤ bonus 289 p := by
  have certified := compare0 p (guard1284 p guard)
  simpa only [at290, at289, Int.zero_add] using certified
theorem check1284 (p : Pattern) : (!walkGuard soko3_2.board support p 290 289 .west || decide (bonus 290 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound1284 p)
theorem guard1285 (p : Pattern) (guard : pushGuard support p 290 289 288 288 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1285 (p : Pattern) (guard : pushGuard support p 290 289 288 288 = true) : bonus 290 p ≤ 1 + Generated.soko3_2Potential.boulder 288 - Generated.soko3_2Potential.boulder 289 + bonus 289 (change p 289 (some 288)) := by
  have certified := compare4301 p (guard1285 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 289 (some 288))
  have normalized := agree134 _ _ (change_representative support p 289 (some 288) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1285 (p : Pattern) : (!pushGuard support p 290 289 288 288 || decide (bonus 290 p ≤ 1 + Generated.soko3_2Potential.boulder 288 - Generated.soko3_2Potential.boulder 289 + bonus 289 (change p 289 (some 288)))) = true :=
  check_of_implication _ _ (bound1285 p)
theorem guard1286 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 265 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1286 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 265 .northEast = true) : bonus 290 p ≤ bonus 265 p := by
  have certified := compare0 p (guard1286 p guard)
  simpa only [at290, at265, Int.zero_add] using certified
theorem check1286 (p : Pattern) : (!walkGuard soko3_2.board support p 290 265 .northEast || decide (bonus 290 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound1286 p)
theorem guard1287 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 263 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1287 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 263 .northWest = true) : bonus 290 p ≤ bonus 263 p := by
  have certified := compare0 p (guard1287 p guard)
  simpa only [at290, at263, Int.zero_add] using certified
theorem check1287 (p : Pattern) : (!walkGuard soko3_2.board support p 290 263 .northWest || decide (bonus 290 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound1287 p)
theorem guard1288 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 317 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1288 (p : Pattern) (guard : walkGuard soko3_2.board support p 290 317 .southEast = true) : bonus 290 p ≤ bonus 317 p := by
  have certified := compare0 p (guard1288 p guard)
  simpa only [at290, at317, Int.zero_add] using certified
theorem check1288 (p : Pattern) : (!walkGuard soko3_2.board support p 290 317 .southEast || decide (bonus 290 p ≤ bonus 317 p)) = true :=
  check_of_implication _ _ (bound1288 p)
theorem guard1289 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 265 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1289 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 265 .north = true) : bonus 291 p ≤ bonus 265 p := by
  have certified := compare0 p (guard1289 p guard)
  simpa only [at291, at265, Int.zero_add] using certified
theorem check1289 (p : Pattern) : (!walkGuard soko3_2.board support p 291 265 .north || decide (bonus 291 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound1289 p)
theorem guard1290 (p : Pattern) (guard : pushGuard support p 291 265 239 239 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1290 (p : Pattern) (guard : pushGuard support p 291 265 239 239 = true) : bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder 239 - Generated.soko3_2Potential.boulder 265 + bonus 265 (change p 265 (some 239)) := by
  have certified := compare4301 p (guard1290 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 265 (some 239))
  have normalized := agree134 _ _ (change_representative support p 265 (some 239) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1290 (p : Pattern) : (!pushGuard support p 291 265 239 239 || decide (bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder 239 - Generated.soko3_2Potential.boulder 265 + bonus 265 (change p 265 (some 239)))) = true :=
  check_of_implication _ _ (bound1290 p)
theorem guard1291 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 317 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1291 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 317 .south = true) : bonus 291 p ≤ bonus 317 p := by
  have certified := compare0 p (guard1291 p guard)
  simpa only [at291, at317, Int.zero_add] using certified
theorem check1291 (p : Pattern) : (!walkGuard soko3_2.board support p 291 317 .south || decide (bonus 291 p ≤ bonus 317 p)) = true :=
  check_of_implication _ _ (bound1291 p)
theorem guard1292 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 292 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1292 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 292 .east = true) : bonus 291 p ≤ bonus 292 p := by
  have certified := compare0 p (guard1292 p guard)
  simpa only [at291, at292, Int.zero_add] using certified
theorem check1292 (p : Pattern) : (!walkGuard soko3_2.board support p 291 292 .east || decide (bonus 291 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound1292 p)
theorem guard1293 (p : Pattern) (guard : pushGuard support p 291 292 293 293 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1293 (p : Pattern) (guard : pushGuard support p 291 292 293 293 = true) : bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder 293 - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some 293)) := by
  have certified := compare0 p (guard1293 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 292 (some 293))
  have normalized := agree134 _ _ (change_representative support p 292 (some 293) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1293 (p : Pattern) : (!pushGuard support p 291 292 293 293 || decide (bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder 293 - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some 293)))) = true :=
  check_of_implication _ _ (bound1293 p)
theorem guard1294 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 290 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1294 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 290 .west = true) : bonus 291 p ≤ bonus 290 p := by
  have certified := compare0 p (guard1294 p guard)
  simpa only [at291, at290, Int.zero_add] using certified
theorem check1294 (p : Pattern) : (!walkGuard soko3_2.board support p 291 290 .west || decide (bonus 291 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound1294 p)
theorem guard1295 (p : Pattern) (guard : pushGuard support p 291 290 289 289 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1295 (p : Pattern) (guard : pushGuard support p 291 290 289 289 = true) : bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder 289 - Generated.soko3_2Potential.boulder 290 + bonus 290 (change p 290 (some 289)) := by
  have certified := compare4301 p (guard1295 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 290 (some 289))
  have normalized := agree134 _ _ (change_representative support p 290 (some 289) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1295 (p : Pattern) : (!pushGuard support p 291 290 289 289 || decide (bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder 289 - Generated.soko3_2Potential.boulder 290 + bonus 290 (change p 290 (some 289)))) = true :=
  check_of_implication _ _ (bound1295 p)
end NetHack.Sokoban32Refined
