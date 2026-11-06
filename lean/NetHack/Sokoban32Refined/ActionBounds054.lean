import NetHack.Sokoban32Refined.ActionBounds053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1296 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 266 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1296 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 266 .northEast = true) : bonus 291 p ≤ bonus 266 p := by
  have certified := compare0 p (guard1296 p guard)
  simpa only [at291, at266, Int.zero_add] using certified
theorem check1296 (p : Pattern) : (!walkGuard soko3_2.board support p 291 266 .northEast || decide (bonus 291 p ≤ bonus 266 p)) = true :=
  check_of_implication _ _ (bound1296 p)
theorem guard1297 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 318 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1297 (p : Pattern) (guard : walkGuard soko3_2.board support p 291 318 .southEast = true) : bonus 291 p ≤ bonus 318 p := by
  have certified := compare0 p (guard1297 p guard)
  simpa only [at291, at318, Int.zero_add] using certified
theorem check1297 (p : Pattern) : (!walkGuard soko3_2.board support p 291 318 .southEast || decide (bonus 291 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound1297 p)
theorem guard1298 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 266 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1298 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 266 .north = true) : bonus 292 p ≤ bonus 266 p := by
  have certified := compare0 p (guard1298 p guard)
  simpa only [at292, at266, Int.zero_add] using certified
theorem check1298 (p : Pattern) : (!walkGuard soko3_2.board support p 292 266 .north || decide (bonus 292 p ≤ bonus 266 p)) = true :=
  check_of_implication _ _ (bound1298 p)
theorem guard1299 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 318 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1299 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 318 .south = true) : bonus 292 p ≤ bonus 318 p := by
  have certified := compare0 p (guard1299 p guard)
  simpa only [at292, at318, Int.zero_add] using certified
theorem check1299 (p : Pattern) : (!walkGuard soko3_2.board support p 292 318 .south || decide (bonus 292 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound1299 p)
theorem guard1300 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 293 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1300 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 293 .east = true) : bonus 292 p ≤ bonus 293 p := by
  have certified := compare0 p (guard1300 p guard)
  simpa only [at292, at293, Int.zero_add] using certified
theorem check1300 (p : Pattern) : (!walkGuard soko3_2.board support p 292 293 .east || decide (bonus 292 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound1300 p)
theorem guard1301 (p : Pattern) (guard : pushGuard support p 292 293 294 294 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1301 (p : Pattern) (guard : pushGuard support p 292 293 294 294 = true) : bonus 292 p ≤ 1 + Generated.soko3_2Potential.boulder 294 - Generated.soko3_2Potential.boulder 293 + bonus 293 (change p 293 (some 294)) := by
  have certified := compare0 p (guard1301 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 293 (some 294))
  have normalized := agree134 _ _ (change_representative support p 293 (some 294) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1301 (p : Pattern) : (!pushGuard support p 292 293 294 294 || decide (bonus 292 p ≤ 1 + Generated.soko3_2Potential.boulder 294 - Generated.soko3_2Potential.boulder 293 + bonus 293 (change p 293 (some 294)))) = true :=
  check_of_implication _ _ (bound1301 p)
theorem guard1302 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 291 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1302 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 291 .west = true) : bonus 292 p ≤ bonus 291 p := by
  have certified := compare0 p (guard1302 p guard)
  simpa only [at292, at291, Int.zero_add] using certified
theorem check1302 (p : Pattern) : (!walkGuard soko3_2.board support p 292 291 .west || decide (bonus 292 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound1302 p)
theorem guard1303 (p : Pattern) (guard : pushGuard support p 292 291 290 290 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1303 (p : Pattern) (guard : pushGuard support p 292 291 290 290 = true) : bonus 292 p ≤ 1 + Generated.soko3_2Potential.boulder 290 - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some 290)) := by
  have certified := compare4301 p (guard1303 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 291 (some 290))
  have normalized := agree134 _ _ (change_representative support p 291 (some 290) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1303 (p : Pattern) : (!pushGuard support p 292 291 290 290 || decide (bonus 292 p ≤ 1 + Generated.soko3_2Potential.boulder 290 - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some 290)))) = true :=
  check_of_implication _ _ (bound1303 p)
theorem guard1304 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 267 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1304 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 267 .northEast = true) : bonus 292 p ≤ bonus 267 p := by
  have certified := compare0 p (guard1304 p guard)
  simpa only [at292, at267, Int.zero_add] using certified
theorem check1304 (p : Pattern) : (!walkGuard soko3_2.board support p 292 267 .northEast || decide (bonus 292 p ≤ bonus 267 p)) = true :=
  check_of_implication _ _ (bound1304 p)
theorem guard1305 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 265 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1305 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 265 .northWest = true) : bonus 292 p ≤ bonus 265 p := by
  have certified := compare0 p (guard1305 p guard)
  simpa only [at292, at265, Int.zero_add] using certified
theorem check1305 (p : Pattern) : (!walkGuard soko3_2.board support p 292 265 .northWest || decide (bonus 292 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound1305 p)
theorem guard1306 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 317 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1306 (p : Pattern) (guard : walkGuard soko3_2.board support p 292 317 .southWest = true) : bonus 292 p ≤ bonus 317 p := by
  have certified := compare0 p (guard1306 p guard)
  simpa only [at292, at317, Int.zero_add] using certified
theorem check1306 (p : Pattern) : (!walkGuard soko3_2.board support p 292 317 .southWest || decide (bonus 292 p ≤ bonus 317 p)) = true :=
  check_of_implication _ _ (bound1306 p)
theorem guard1307 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 267 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1307 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 267 .north = true) : bonus 293 p ≤ bonus 267 p := by
  have certified := compare0 p (guard1307 p guard)
  simpa only [at293, at267, Int.zero_add] using certified
theorem check1307 (p : Pattern) : (!walkGuard soko3_2.board support p 293 267 .north || decide (bonus 293 p ≤ bonus 267 p)) = true :=
  check_of_implication _ _ (bound1307 p)
theorem guard1308 (p : Pattern) (guard : pushGuard support p 293 267 241 241 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1308 (p : Pattern) (guard : pushGuard support p 293 267 241 241 = true) : bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder 241 - Generated.soko3_2Potential.boulder 267 + bonus 267 (change p 267 (some 241)) := by
  have certified := compare4301 p (guard1308 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 267 (some 241))
  have normalized := agree134 _ _ (change_representative support p 267 (some 241) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1308 (p : Pattern) : (!pushGuard support p 293 267 241 241 || decide (bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder 241 - Generated.soko3_2Potential.boulder 267 + bonus 267 (change p 267 (some 241)))) = true :=
  check_of_implication _ _ (bound1308 p)
theorem guard1309 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 294 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1309 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 294 .east = true) : bonus 293 p ≤ bonus 294 p := by
  have certified := compare0 p (guard1309 p guard)
  simpa only [at293, at294, Int.zero_add] using certified
theorem check1309 (p : Pattern) : (!walkGuard soko3_2.board support p 293 294 .east || decide (bonus 293 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound1309 p)
theorem guard1310 (p : Pattern) (guard : pushGuard support p 293 294 295 295 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1310 (p : Pattern) (guard : pushGuard support p 293 294 295 295 = true) : bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder 295 - Generated.soko3_2Potential.boulder 294 + bonus 294 (change p 294 (some 295)) := by
  have certified := compare0 p (guard1310 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 294 (some 295))
  have normalized := agree134 _ _ (change_representative support p 294 (some 295) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1310 (p : Pattern) : (!pushGuard support p 293 294 295 295 || decide (bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder 295 - Generated.soko3_2Potential.boulder 294 + bonus 294 (change p 294 (some 295)))) = true :=
  check_of_implication _ _ (bound1310 p)
theorem guard1311 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 292 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1311 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 292 .west = true) : bonus 293 p ≤ bonus 292 p := by
  have certified := compare0 p (guard1311 p guard)
  simpa only [at293, at292, Int.zero_add] using certified
theorem check1311 (p : Pattern) : (!walkGuard soko3_2.board support p 293 292 .west || decide (bonus 293 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound1311 p)
theorem guard1312 (p : Pattern) (guard : pushGuard support p 293 292 291 291 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1312 (p : Pattern) (guard : pushGuard support p 293 292 291 291 = true) : bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some 291)) := by
  have certified := compare4301 p (guard1312 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 292 (some 291))
  have normalized := agree134 _ _ (change_representative support p 292 (some 291) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1312 (p : Pattern) : (!pushGuard support p 293 292 291 291 || decide (bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some 291)))) = true :=
  check_of_implication _ _ (bound1312 p)
theorem guard1313 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 266 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1313 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 266 .northWest = true) : bonus 293 p ≤ bonus 266 p := by
  have certified := compare0 p (guard1313 p guard)
  simpa only [at293, at266, Int.zero_add] using certified
theorem check1313 (p : Pattern) : (!walkGuard soko3_2.board support p 293 266 .northWest || decide (bonus 293 p ≤ bonus 266 p)) = true :=
  check_of_implication _ _ (bound1313 p)
theorem guard1314 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 320 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1314 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 320 .southEast = true) : bonus 293 p ≤ bonus 320 p := by
  have certified := compare0 p (guard1314 p guard)
  simpa only [at293, at320, Int.zero_add] using certified
theorem check1314 (p : Pattern) : (!walkGuard soko3_2.board support p 293 320 .southEast || decide (bonus 293 p ≤ bonus 320 p)) = true :=
  check_of_implication _ _ (bound1314 p)
theorem guard1315 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 318 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1315 (p : Pattern) (guard : walkGuard soko3_2.board support p 293 318 .southWest = true) : bonus 293 p ≤ bonus 318 p := by
  have certified := compare0 p (guard1315 p guard)
  simpa only [at293, at318, Int.zero_add] using certified
theorem check1315 (p : Pattern) : (!walkGuard soko3_2.board support p 293 318 .southWest || decide (bonus 293 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound1315 p)
theorem guard1316 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 320 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1316 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 320 .south = true) : bonus 294 p ≤ bonus 320 p := by
  have certified := compare0 p (guard1316 p guard)
  simpa only [at294, at320, Int.zero_add] using certified
theorem check1316 (p : Pattern) : (!walkGuard soko3_2.board support p 294 320 .south || decide (bonus 294 p ≤ bonus 320 p)) = true :=
  check_of_implication _ _ (bound1316 p)
theorem guard1317 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 295 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1317 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 295 .east = true) : bonus 294 p ≤ bonus 295 p := by
  have certified := compare0 p (guard1317 p guard)
  simpa only [at294, at295, Int.zero_add] using certified
theorem check1317 (p : Pattern) : (!walkGuard soko3_2.board support p 294 295 .east || decide (bonus 294 p ≤ bonus 295 p)) = true :=
  check_of_implication _ _ (bound1317 p)
theorem guard1318 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 293 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1318 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 293 .west = true) : bonus 294 p ≤ bonus 293 p := by
  have certified := compare0 p (guard1318 p guard)
  simpa only [at294, at293, Int.zero_add] using certified
theorem check1318 (p : Pattern) : (!walkGuard soko3_2.board support p 294 293 .west || decide (bonus 294 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound1318 p)
theorem guard1319 (p : Pattern) (guard : pushGuard support p 294 293 292 292 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1319 (p : Pattern) (guard : pushGuard support p 294 293 292 292 = true) : bonus 294 p ≤ 1 + Generated.soko3_2Potential.boulder 292 - Generated.soko3_2Potential.boulder 293 + bonus 293 (change p 293 (some 292)) := by
  have certified := compare4301 p (guard1319 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 293 (some 292))
  have normalized := agree134 _ _ (change_representative support p 293 (some 292) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1319 (p : Pattern) : (!pushGuard support p 294 293 292 292 || decide (bonus 294 p ≤ 1 + Generated.soko3_2Potential.boulder 292 - Generated.soko3_2Potential.boulder 293 + bonus 293 (change p 293 (some 292)))) = true :=
  check_of_implication _ _ (bound1319 p)
end NetHack.Sokoban32Refined
