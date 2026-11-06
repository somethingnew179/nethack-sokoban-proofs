import NetHack.Sokoban32Refined.ActionBounds051
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1248 (p : Pattern) (guard : pushGuard support p 281 282 283 283 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1248 (p : Pattern) (guard : pushGuard support p 281 282 283 283 = true) : bonus 281 p ≤ 1 + Generated.soko3_2Potential.boulder 283 - Generated.soko3_2Potential.boulder 282 + bonus 282 (change p 282 (some 283)) := by
  have certified := compare104 p (guard1248 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 282 (some 283))
  have normalized := agree134 _ _ (change_representative support p 282 (some 283) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1248 (p : Pattern) : (!pushGuard support p 281 282 283 283 || decide (bonus 281 p ≤ 1 + Generated.soko3_2Potential.boulder 283 - Generated.soko3_2Potential.boulder 282 + bonus 282 (change p 282 (some 283)))) = true :=
  check_of_implication _ _ (bound1248 p)
theorem guard1249 (p : Pattern) (guard : pushGuard support p 281 282 283 283 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1249 (p : Pattern) (guard : pushGuard support p 281 282 283 283 = true) : bonus 281 p ≤ 1 - Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.hole 283 + bonus 282 (change p 282 none) := by
  have certified := compare104 p (guard1249 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 282 none)
  have normalized := agree134 _ _ (change_representative support p 282 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1249 (p : Pattern) : (!pushGuard support p 281 282 283 283 || decide (bonus 281 p ≤ 1 - Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.hole 283 + bonus 282 (change p 282 none))) = true :=
  check_of_implication _ _ (bound1249 p)
theorem guard1250 (p : Pattern) (guard : walkGuard soko3_2.board support p 281 280 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1250 (p : Pattern) (guard : walkGuard soko3_2.board support p 281 280 .west = true) : bonus 281 p ≤ bonus 280 p := by
  have certified := compare0 p (guard1250 p guard)
  simpa only [at281, at280, Int.zero_add] using certified
theorem check1250 (p : Pattern) : (!walkGuard soko3_2.board support p 281 280 .west || decide (bonus 281 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound1250 p)
theorem guard1251 (p : Pattern) (guard : pushGuard support p 281 280 279 279 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1251 (p : Pattern) (guard : pushGuard support p 281 280 279 279 = true) : bonus 281 p ≤ 1 + Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.boulder 280 + bonus 280 (change p 280 (some 279)) := by
  have certified := compare104 p (guard1251 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 280 (some 279))
  have normalized := agree134 _ _ (change_representative support p 280 (some 279) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1251 (p : Pattern) : (!pushGuard support p 281 280 279 279 || decide (bonus 281 p ≤ 1 + Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.boulder 280 + bonus 280 (change p 280 (some 279)))) = true :=
  check_of_implication _ _ (bound1251 p)
theorem guard1252 (p : Pattern) (guard : pushGuard support p 281 280 279 279 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1252 (p : Pattern) (guard : pushGuard support p 281 280 279 279 = true) : bonus 281 p ≤ 1 - Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.hole 279 + bonus 280 (change p 280 none) := by
  have certified := compare104 p (guard1252 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 280 none)
  have normalized := agree134 _ _ (change_representative support p 280 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1252 (p : Pattern) : (!pushGuard support p 281 280 279 279 || decide (bonus 281 p ≤ 1 - Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.hole 279 + bonus 280 (change p 280 none))) = true :=
  check_of_implication _ _ (bound1252 p)
theorem guard1253 (p : Pattern) (guard : walkGuard soko3_2.board support p 282 283 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1253 (p : Pattern) (guard : walkGuard soko3_2.board support p 282 283 .east = true) : bonus 282 p ≤ bonus 283 p := by
  have certified := compare0 p (guard1253 p guard)
  simpa only [at282, at283, Int.zero_add] using certified
theorem check1253 (p : Pattern) : (!walkGuard soko3_2.board support p 282 283 .east || decide (bonus 282 p ≤ bonus 283 p)) = true :=
  check_of_implication _ _ (bound1253 p)
theorem guard1254 (p : Pattern) (guard : pushGuard support p 282 283 284 284 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1254 (p : Pattern) (guard : pushGuard support p 282 283 284 284 = true) : bonus 282 p ≤ 1 + Generated.soko3_2Potential.boulder 284 - Generated.soko3_2Potential.boulder 283 + bonus 283 (change p 283 (some 284)) := by
  have certified := compare9369 p (guard1254 p guard)
  change d134 p ≤ (19 : Int) + d134 (change p 283 (some 284))
  have normalized := agree134 _ _ (change_representative support p 283 (some 284) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (19 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1254 (p : Pattern) : (!pushGuard support p 282 283 284 284 || decide (bonus 282 p ≤ 1 + Generated.soko3_2Potential.boulder 284 - Generated.soko3_2Potential.boulder 283 + bonus 283 (change p 283 (some 284)))) = true :=
  check_of_implication _ _ (bound1254 p)
theorem guard1255 (p : Pattern) (guard : walkGuard soko3_2.board support p 282 281 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1255 (p : Pattern) (guard : walkGuard soko3_2.board support p 282 281 .west = true) : bonus 282 p ≤ bonus 281 p := by
  have certified := compare0 p (guard1255 p guard)
  simpa only [at282, at281, Int.zero_add] using certified
theorem check1255 (p : Pattern) : (!walkGuard soko3_2.board support p 282 281 .west || decide (bonus 282 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound1255 p)
theorem guard1256 (p : Pattern) (guard : pushGuard support p 282 281 280 280 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1256 (p : Pattern) (guard : pushGuard support p 282 281 280 280 = true) : bonus 282 p ≤ 1 + Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.boulder 281 + bonus 281 (change p 281 (some 280)) := by
  have certified := compare104 p (guard1256 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 281 (some 280))
  have normalized := agree134 _ _ (change_representative support p 281 (some 280) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1256 (p : Pattern) : (!pushGuard support p 282 281 280 280 || decide (bonus 282 p ≤ 1 + Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.boulder 281 + bonus 281 (change p 281 (some 280)))) = true :=
  check_of_implication _ _ (bound1256 p)
theorem guard1257 (p : Pattern) (guard : pushGuard support p 282 281 280 280 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1257 (p : Pattern) (guard : pushGuard support p 282 281 280 280 = true) : bonus 282 p ≤ 1 - Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.hole 280 + bonus 281 (change p 281 none) := by
  have certified := compare104 p (guard1257 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 281 none)
  have normalized := agree134 _ _ (change_representative support p 281 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1257 (p : Pattern) : (!pushGuard support p 282 281 280 280 || decide (bonus 282 p ≤ 1 - Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.hole 280 + bonus 281 (change p 281 none))) = true :=
  check_of_implication _ _ (bound1257 p)
theorem guard1258 (p : Pattern) (guard : walkGuard soko3_2.board support p 283 284 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1258 (p : Pattern) (guard : walkGuard soko3_2.board support p 283 284 .east = true) : bonus 283 p ≤ bonus 284 p := by
  have certified := compare0 p (guard1258 p guard)
  simpa only [at283, at284, Int.zero_add] using certified
theorem check1258 (p : Pattern) : (!walkGuard soko3_2.board support p 283 284 .east || decide (bonus 283 p ≤ bonus 284 p)) = true :=
  check_of_implication _ _ (bound1258 p)
theorem guard1259 (p : Pattern) (guard : walkGuard soko3_2.board support p 283 282 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1259 (p : Pattern) (guard : walkGuard soko3_2.board support p 283 282 .west = true) : bonus 283 p ≤ bonus 282 p := by
  have certified := compare0 p (guard1259 p guard)
  simpa only [at283, at282, Int.zero_add] using certified
theorem check1259 (p : Pattern) : (!walkGuard soko3_2.board support p 283 282 .west || decide (bonus 283 p ≤ bonus 282 p)) = true :=
  check_of_implication _ _ (bound1259 p)
theorem guard1260 (p : Pattern) (guard : pushGuard support p 283 282 281 281 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1260 (p : Pattern) (guard : pushGuard support p 283 282 281 281 = true) : bonus 283 p ≤ 1 + Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.boulder 282 + bonus 282 (change p 282 (some 281)) := by
  have certified := compare104 p (guard1260 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 282 (some 281))
  have normalized := agree134 _ _ (change_representative support p 282 (some 281) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1260 (p : Pattern) : (!pushGuard support p 283 282 281 281 || decide (bonus 283 p ≤ 1 + Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.boulder 282 + bonus 282 (change p 282 (some 281)))) = true :=
  check_of_implication _ _ (bound1260 p)
theorem guard1261 (p : Pattern) (guard : pushGuard support p 283 282 281 281 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1261 (p : Pattern) (guard : pushGuard support p 283 282 281 281 = true) : bonus 283 p ≤ 1 - Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.hole 281 + bonus 282 (change p 282 none) := by
  have certified := compare104 p (guard1261 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 282 none)
  have normalized := agree134 _ _ (change_representative support p 282 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1261 (p : Pattern) : (!pushGuard support p 283 282 281 281 || decide (bonus 283 p ≤ 1 - Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.hole 281 + bonus 282 (change p 282 none))) = true :=
  check_of_implication _ _ (bound1261 p)
theorem guard1262 (p : Pattern) (guard : walkGuard soko3_2.board support p 284 283 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1262 (p : Pattern) (guard : walkGuard soko3_2.board support p 284 283 .west = true) : bonus 284 p ≤ bonus 283 p := by
  have certified := compare0 p (guard1262 p guard)
  simpa only [at284, at283, Int.zero_add] using certified
theorem check1262 (p : Pattern) : (!walkGuard soko3_2.board support p 284 283 .west || decide (bonus 284 p ≤ bonus 283 p)) = true :=
  check_of_implication _ _ (bound1262 p)
theorem guard1263 (p : Pattern) (guard : pushGuard support p 284 283 282 282 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1263 (p : Pattern) (guard : pushGuard support p 284 283 282 282 = true) : bonus 284 p ≤ 1 + Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.boulder 283 + bonus 283 (change p 283 (some 282)) := by
  have certified := compare104 p (guard1263 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 283 (some 282))
  have normalized := agree134 _ _ (change_representative support p 283 (some 282) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1263 (p : Pattern) : (!pushGuard support p 284 283 282 282 || decide (bonus 284 p ≤ 1 + Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.boulder 283 + bonus 283 (change p 283 (some 282)))) = true :=
  check_of_implication _ _ (bound1263 p)
theorem guard1264 (p : Pattern) (guard : pushGuard support p 284 283 282 282 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1264 (p : Pattern) (guard : pushGuard support p 284 283 282 282 = true) : bonus 284 p ≤ 1 - Generated.soko3_2Potential.boulder 283 - Generated.soko3_2Potential.hole 282 + bonus 283 (change p 283 none) := by
  have certified := compare104 p (guard1264 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 283 none)
  have normalized := agree134 _ _ (change_representative support p 283 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1264 (p : Pattern) : (!pushGuard support p 284 283 282 282 || decide (bonus 284 p ≤ 1 - Generated.soko3_2Potential.boulder 283 - Generated.soko3_2Potential.hole 282 + bonus 283 (change p 283 none))) = true :=
  check_of_implication _ _ (bound1264 p)
theorem guard1265 (p : Pattern) (guard : walkGuard soko3_2.board support p 287 261 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1265 (p : Pattern) (guard : walkGuard soko3_2.board support p 287 261 .north = true) : bonus 287 p ≤ bonus 261 p := by
  have certified := compare0 p (guard1265 p guard)
  simpa only [at287, at261, Int.zero_add] using certified
theorem check1265 (p : Pattern) : (!walkGuard soko3_2.board support p 287 261 .north || decide (bonus 287 p ≤ bonus 261 p)) = true :=
  check_of_implication _ _ (bound1265 p)
theorem guard1266 (p : Pattern) (guard : pushGuard support p 287 261 235 235 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1266 (p : Pattern) (guard : pushGuard support p 287 261 235 235 = true) : bonus 287 p ≤ 1 + Generated.soko3_2Potential.boulder 235 - Generated.soko3_2Potential.boulder 261 + bonus 261 (change p 261 (some 235)) := by
  have certified := compare104 p (guard1266 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 261 (some 235))
  have normalized := agree134 _ _ (change_representative support p 261 (some 235) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1266 (p : Pattern) : (!pushGuard support p 287 261 235 235 || decide (bonus 287 p ≤ 1 + Generated.soko3_2Potential.boulder 235 - Generated.soko3_2Potential.boulder 261 + bonus 261 (change p 261 (some 235)))) = true :=
  check_of_implication _ _ (bound1266 p)
theorem guard1267 (p : Pattern) (guard : walkGuard soko3_2.board support p 287 288 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1267 (p : Pattern) (guard : walkGuard soko3_2.board support p 287 288 .east = true) : bonus 287 p ≤ bonus 288 p := by
  have certified := compare0 p (guard1267 p guard)
  simpa only [at287, at288, Int.zero_add] using certified
theorem check1267 (p : Pattern) : (!walkGuard soko3_2.board support p 287 288 .east || decide (bonus 287 p ≤ bonus 288 p)) = true :=
  check_of_implication _ _ (bound1267 p)
theorem guard1268 (p : Pattern) (guard : pushGuard support p 287 288 289 289 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1268 (p : Pattern) (guard : pushGuard support p 287 288 289 289 = true) : bonus 287 p ≤ 1 + Generated.soko3_2Potential.boulder 289 - Generated.soko3_2Potential.boulder 288 + bonus 288 (change p 288 (some 289)) := by
  have certified := compare0 p (guard1268 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 288 (some 289))
  have normalized := agree134 _ _ (change_representative support p 288 (some 289) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1268 (p : Pattern) : (!pushGuard support p 287 288 289 289 || decide (bonus 287 p ≤ 1 + Generated.soko3_2Potential.boulder 289 - Generated.soko3_2Potential.boulder 288 + bonus 288 (change p 288 (some 289)))) = true :=
  check_of_implication _ _ (bound1268 p)
theorem guard1269 (p : Pattern) (guard : walkGuard soko3_2.board support p 287 262 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1269 (p : Pattern) (guard : walkGuard soko3_2.board support p 287 262 .northEast = true) : bonus 287 p ≤ bonus 262 p := by
  have certified := compare0 p (guard1269 p guard)
  simpa only [at287, at262, Int.zero_add] using certified
theorem check1269 (p : Pattern) : (!walkGuard soko3_2.board support p 287 262 .northEast || decide (bonus 287 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound1269 p)
theorem guard1270 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 262 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1270 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 262 .north = true) : bonus 288 p ≤ bonus 262 p := by
  have certified := compare0 p (guard1270 p guard)
  simpa only [at288, at262, Int.zero_add] using certified
theorem check1270 (p : Pattern) : (!walkGuard soko3_2.board support p 288 262 .north || decide (bonus 288 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound1270 p)
theorem guard1271 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 289 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1271 (p : Pattern) (guard : walkGuard soko3_2.board support p 288 289 .east = true) : bonus 288 p ≤ bonus 289 p := by
  have certified := compare0 p (guard1271 p guard)
  simpa only [at288, at289, Int.zero_add] using certified
theorem check1271 (p : Pattern) : (!walkGuard soko3_2.board support p 288 289 .east || decide (bonus 288 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound1271 p)
end NetHack.Sokoban32Refined
