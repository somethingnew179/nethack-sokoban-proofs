import NetHack.Sokoban32Refined.ActionBounds054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1320 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 269 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1320 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 269 .northEast = true) : bonus 294 p ≤ bonus 269 p := by
  have certified := compare0 p (guard1320 p guard)
  simpa only [at294, at269, Int.zero_add] using certified
theorem check1320 (p : Pattern) : (!walkGuard soko3_2.board support p 294 269 .northEast || decide (bonus 294 p ≤ bonus 269 p)) = true :=
  check_of_implication _ _ (bound1320 p)
theorem guard1321 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 267 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1321 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 267 .northWest = true) : bonus 294 p ≤ bonus 267 p := by
  have certified := compare0 p (guard1321 p guard)
  simpa only [at294, at267, Int.zero_add] using certified
theorem check1321 (p : Pattern) : (!walkGuard soko3_2.board support p 294 267 .northWest || decide (bonus 294 p ≤ bonus 267 p)) = true :=
  check_of_implication _ _ (bound1321 p)
theorem guard1322 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 321 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1322 (p : Pattern) (guard : walkGuard soko3_2.board support p 294 321 .southEast = true) : bonus 294 p ≤ bonus 321 p := by
  have certified := compare0 p (guard1322 p guard)
  simpa only [at294, at321, Int.zero_add] using certified
theorem check1322 (p : Pattern) : (!walkGuard soko3_2.board support p 294 321 .southEast || decide (bonus 294 p ≤ bonus 321 p)) = true :=
  check_of_implication _ _ (bound1322 p)
theorem guard1323 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 269 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1323 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 269 .north = true) : bonus 295 p ≤ bonus 269 p := by
  have certified := compare0 p (guard1323 p guard)
  simpa only [at295, at269, Int.zero_add] using certified
theorem check1323 (p : Pattern) : (!walkGuard soko3_2.board support p 295 269 .north || decide (bonus 295 p ≤ bonus 269 p)) = true :=
  check_of_implication _ _ (bound1323 p)
theorem guard1324 (p : Pattern) (guard : pushGuard support p 295 269 243 243 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1324 (p : Pattern) (guard : pushGuard support p 295 269 243 243 = true) : bonus 295 p ≤ 1 + Generated.soko3_2Potential.boulder 243 - Generated.soko3_2Potential.boulder 269 + bonus 269 (change p 269 (some 243)) := by
  have certified := compare0 p (guard1324 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 269 (some 243))
  have normalized := agree134 _ _ (change_representative support p 269 (some 243) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1324 (p : Pattern) : (!pushGuard support p 295 269 243 243 || decide (bonus 295 p ≤ 1 + Generated.soko3_2Potential.boulder 243 - Generated.soko3_2Potential.boulder 269 + bonus 269 (change p 269 (some 243)))) = true :=
  check_of_implication _ _ (bound1324 p)
theorem guard1325 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 321 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1325 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 321 .south = true) : bonus 295 p ≤ bonus 321 p := by
  have certified := compare0 p (guard1325 p guard)
  simpa only [at295, at321, Int.zero_add] using certified
theorem check1325 (p : Pattern) : (!walkGuard soko3_2.board support p 295 321 .south || decide (bonus 295 p ≤ bonus 321 p)) = true :=
  check_of_implication _ _ (bound1325 p)
theorem guard1326 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 294 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1326 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 294 .west = true) : bonus 295 p ≤ bonus 294 p := by
  have certified := compare0 p (guard1326 p guard)
  simpa only [at295, at294, Int.zero_add] using certified
theorem check1326 (p : Pattern) : (!walkGuard soko3_2.board support p 295 294 .west || decide (bonus 295 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound1326 p)
theorem guard1327 (p : Pattern) (guard : pushGuard support p 295 294 293 293 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1327 (p : Pattern) (guard : pushGuard support p 295 294 293 293 = true) : bonus 295 p ≤ 1 + Generated.soko3_2Potential.boulder 293 - Generated.soko3_2Potential.boulder 294 + bonus 294 (change p 294 (some 293)) := by
  have certified := compare4301 p (guard1327 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 294 (some 293))
  have normalized := agree134 _ _ (change_representative support p 294 (some 293) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1327 (p : Pattern) : (!pushGuard support p 295 294 293 293 || decide (bonus 295 p ≤ 1 + Generated.soko3_2Potential.boulder 293 - Generated.soko3_2Potential.boulder 294 + bonus 294 (change p 294 (some 293)))) = true :=
  check_of_implication _ _ (bound1327 p)
theorem guard1328 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 270 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1328 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 270 .northEast = true) : bonus 295 p ≤ bonus 270 p := by
  have certified := compare0 p (guard1328 p guard)
  simpa only [at295, at270, Int.zero_add] using certified
theorem check1328 (p : Pattern) : (!walkGuard soko3_2.board support p 295 270 .northEast || decide (bonus 295 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound1328 p)
theorem guard1329 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 320 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1329 (p : Pattern) (guard : walkGuard soko3_2.board support p 295 320 .southWest = true) : bonus 295 p ≤ bonus 320 p := by
  have certified := compare0 p (guard1329 p guard)
  simpa only [at295, at320, Int.zero_add] using certified
theorem check1329 (p : Pattern) : (!walkGuard soko3_2.board support p 295 320 .southWest || decide (bonus 295 p ≤ bonus 320 p)) = true :=
  check_of_implication _ _ (bound1329 p)
theorem guard1330 (p : Pattern) (guard : walkGuard soko3_2.board support p 317 291 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1330 (p : Pattern) (guard : walkGuard soko3_2.board support p 317 291 .north = true) : bonus 317 p ≤ bonus 291 p := by
  have certified := compare0 p (guard1330 p guard)
  simpa only [at317, at291, Int.zero_add] using certified
theorem check1330 (p : Pattern) : (!walkGuard soko3_2.board support p 317 291 .north || decide (bonus 317 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound1330 p)
theorem guard1331 (p : Pattern) (guard : pushGuard support p 317 291 265 265 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1331 (p : Pattern) (guard : pushGuard support p 317 291 265 265 = true) : bonus 317 p ≤ 1 + Generated.soko3_2Potential.boulder 265 - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some 265)) := by
  have certified := compare4301 p (guard1331 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 291 (some 265))
  have normalized := agree134 _ _ (change_representative support p 291 (some 265) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1331 (p : Pattern) : (!pushGuard support p 317 291 265 265 || decide (bonus 317 p ≤ 1 + Generated.soko3_2Potential.boulder 265 - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some 265)))) = true :=
  check_of_implication _ _ (bound1331 p)
theorem guard1332 (p : Pattern) (guard : walkGuard soko3_2.board support p 317 318 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1332 (p : Pattern) (guard : walkGuard soko3_2.board support p 317 318 .east = true) : bonus 317 p ≤ bonus 318 p := by
  have certified := compare0 p (guard1332 p guard)
  simpa only [at317, at318, Int.zero_add] using certified
theorem check1332 (p : Pattern) : (!walkGuard soko3_2.board support p 317 318 .east || decide (bonus 317 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound1332 p)
theorem guard1333 (p : Pattern) (guard : walkGuard soko3_2.board support p 317 292 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1333 (p : Pattern) (guard : walkGuard soko3_2.board support p 317 292 .northEast = true) : bonus 317 p ≤ bonus 292 p := by
  have certified := compare0 p (guard1333 p guard)
  simpa only [at317, at292, Int.zero_add] using certified
theorem check1333 (p : Pattern) : (!walkGuard soko3_2.board support p 317 292 .northEast || decide (bonus 317 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound1333 p)
theorem guard1334 (p : Pattern) (guard : walkGuard soko3_2.board support p 317 290 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1334 (p : Pattern) (guard : walkGuard soko3_2.board support p 317 290 .northWest = true) : bonus 317 p ≤ bonus 290 p := by
  have certified := compare0 p (guard1334 p guard)
  simpa only [at317, at290, Int.zero_add] using certified
theorem check1334 (p : Pattern) : (!walkGuard soko3_2.board support p 317 290 .northWest || decide (bonus 317 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound1334 p)
theorem guard1335 (p : Pattern) (guard : walkGuard soko3_2.board support p 318 292 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1335 (p : Pattern) (guard : walkGuard soko3_2.board support p 318 292 .north = true) : bonus 318 p ≤ bonus 292 p := by
  have certified := compare0 p (guard1335 p guard)
  simpa only [at318, at292, Int.zero_add] using certified
theorem check1335 (p : Pattern) : (!walkGuard soko3_2.board support p 318 292 .north || decide (bonus 318 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound1335 p)
theorem guard1336 (p : Pattern) (guard : pushGuard support p 318 292 266 266 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1336 (p : Pattern) (guard : pushGuard support p 318 292 266 266 = true) : bonus 318 p ≤ 1 + Generated.soko3_2Potential.boulder 266 - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some 266)) := by
  have certified := compare4301 p (guard1336 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 292 (some 266))
  have normalized := agree134 _ _ (change_representative support p 292 (some 266) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1336 (p : Pattern) : (!pushGuard support p 318 292 266 266 || decide (bonus 318 p ≤ 1 + Generated.soko3_2Potential.boulder 266 - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some 266)))) = true :=
  check_of_implication _ _ (bound1336 p)
theorem guard1337 (p : Pattern) (guard : walkGuard soko3_2.board support p 318 317 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1337 (p : Pattern) (guard : walkGuard soko3_2.board support p 318 317 .west = true) : bonus 318 p ≤ bonus 317 p := by
  have certified := compare0 p (guard1337 p guard)
  simpa only [at318, at317, Int.zero_add] using certified
theorem check1337 (p : Pattern) : (!walkGuard soko3_2.board support p 318 317 .west || decide (bonus 318 p ≤ bonus 317 p)) = true :=
  check_of_implication _ _ (bound1337 p)
theorem guard1338 (p : Pattern) (guard : walkGuard soko3_2.board support p 318 293 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1338 (p : Pattern) (guard : walkGuard soko3_2.board support p 318 293 .northEast = true) : bonus 318 p ≤ bonus 293 p := by
  have certified := compare0 p (guard1338 p guard)
  simpa only [at318, at293, Int.zero_add] using certified
theorem check1338 (p : Pattern) : (!walkGuard soko3_2.board support p 318 293 .northEast || decide (bonus 318 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound1338 p)
theorem guard1339 (p : Pattern) (guard : walkGuard soko3_2.board support p 318 291 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1339 (p : Pattern) (guard : walkGuard soko3_2.board support p 318 291 .northWest = true) : bonus 318 p ≤ bonus 291 p := by
  have certified := compare0 p (guard1339 p guard)
  simpa only [at318, at291, Int.zero_add] using certified
theorem check1339 (p : Pattern) : (!walkGuard soko3_2.board support p 318 291 .northWest || decide (bonus 318 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound1339 p)
theorem guard1340 (p : Pattern) (guard : walkGuard soko3_2.board support p 320 294 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1340 (p : Pattern) (guard : walkGuard soko3_2.board support p 320 294 .north = true) : bonus 320 p ≤ bonus 294 p := by
  have certified := compare0 p (guard1340 p guard)
  simpa only [at320, at294, Int.zero_add] using certified
theorem check1340 (p : Pattern) : (!walkGuard soko3_2.board support p 320 294 .north || decide (bonus 320 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound1340 p)
theorem guard1341 (p : Pattern) (guard : walkGuard soko3_2.board support p 320 321 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1341 (p : Pattern) (guard : walkGuard soko3_2.board support p 320 321 .east = true) : bonus 320 p ≤ bonus 321 p := by
  have certified := compare0 p (guard1341 p guard)
  simpa only [at320, at321, Int.zero_add] using certified
theorem check1341 (p : Pattern) : (!walkGuard soko3_2.board support p 320 321 .east || decide (bonus 320 p ≤ bonus 321 p)) = true :=
  check_of_implication _ _ (bound1341 p)
theorem guard1342 (p : Pattern) (guard : walkGuard soko3_2.board support p 320 295 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1342 (p : Pattern) (guard : walkGuard soko3_2.board support p 320 295 .northEast = true) : bonus 320 p ≤ bonus 295 p := by
  have certified := compare0 p (guard1342 p guard)
  simpa only [at320, at295, Int.zero_add] using certified
theorem check1342 (p : Pattern) : (!walkGuard soko3_2.board support p 320 295 .northEast || decide (bonus 320 p ≤ bonus 295 p)) = true :=
  check_of_implication _ _ (bound1342 p)
theorem guard1343 (p : Pattern) (guard : walkGuard soko3_2.board support p 320 293 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1343 (p : Pattern) (guard : walkGuard soko3_2.board support p 320 293 .northWest = true) : bonus 320 p ≤ bonus 293 p := by
  have certified := compare0 p (guard1343 p guard)
  simpa only [at320, at293, Int.zero_add] using certified
theorem check1343 (p : Pattern) : (!walkGuard soko3_2.board support p 320 293 .northWest || decide (bonus 320 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound1343 p)
end NetHack.Sokoban32Refined
