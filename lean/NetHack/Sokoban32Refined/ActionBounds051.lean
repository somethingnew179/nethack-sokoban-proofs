import NetHack.Sokoban32Refined.ActionBounds050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1224 (p : Pattern) (guard : pushGuard support p 277 278 279 279 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1224 (p : Pattern) (guard : pushGuard support p 277 278 279 279 = true) : bonus 277 p ≤ 1 + Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.boulder 278 + bonus 278 (change p 278 (some 279)) := by
  have certified := compare104 p (guard1224 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 278 (some 279))
  have normalized := agree134 _ _ (change_representative support p 278 (some 279) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1224 (p : Pattern) : (!pushGuard support p 277 278 279 279 || decide (bonus 277 p ≤ 1 + Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.boulder 278 + bonus 278 (change p 278 (some 279)))) = true :=
  check_of_implication _ _ (bound1224 p)
theorem guard1225 (p : Pattern) (guard : pushGuard support p 277 278 279 279 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1225 (p : Pattern) (guard : pushGuard support p 277 278 279 279 = true) : bonus 277 p ≤ 1 - Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.hole 279 + bonus 278 (change p 278 none) := by
  have certified := compare104 p (guard1225 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 278 none)
  have normalized := agree134 _ _ (change_representative support p 278 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1225 (p : Pattern) : (!pushGuard support p 277 278 279 279 || decide (bonus 277 p ≤ 1 - Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.hole 279 + bonus 278 (change p 278 none))) = true :=
  check_of_implication _ _ (bound1225 p)
theorem guard1226 (p : Pattern) (guard : walkGuard soko3_2.board support p 277 276 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1226 (p : Pattern) (guard : walkGuard soko3_2.board support p 277 276 .west = true) : bonus 277 p ≤ bonus 276 p := by
  have certified := compare0 p (guard1226 p guard)
  simpa only [at277, at276, Int.zero_add] using certified
theorem check1226 (p : Pattern) : (!walkGuard soko3_2.board support p 277 276 .west || decide (bonus 277 p ≤ bonus 276 p)) = true :=
  check_of_implication _ _ (bound1226 p)
theorem guard1227 (p : Pattern) (guard : pushGuard support p 277 276 275 275 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1227 (p : Pattern) (guard : pushGuard support p 277 276 275 275 = true) : bonus 277 p ≤ 1 + Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.boulder 276 + bonus 276 (change p 276 (some 275)) := by
  have certified := compare104 p (guard1227 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 276 (some 275))
  have normalized := agree134 _ _ (change_representative support p 276 (some 275) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1227 (p : Pattern) : (!pushGuard support p 277 276 275 275 || decide (bonus 277 p ≤ 1 + Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.boulder 276 + bonus 276 (change p 276 (some 275)))) = true :=
  check_of_implication _ _ (bound1227 p)
theorem guard1228 (p : Pattern) (guard : pushGuard support p 277 276 275 275 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1228 (p : Pattern) (guard : pushGuard support p 277 276 275 275 = true) : bonus 277 p ≤ 1 - Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.hole 275 + bonus 276 (change p 276 none) := by
  have certified := compare104 p (guard1228 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 276 none)
  have normalized := agree134 _ _ (change_representative support p 276 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1228 (p : Pattern) : (!pushGuard support p 277 276 275 275 || decide (bonus 277 p ≤ 1 - Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.hole 275 + bonus 276 (change p 276 none))) = true :=
  check_of_implication _ _ (bound1228 p)
theorem guard1229 (p : Pattern) (guard : walkGuard soko3_2.board support p 278 279 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1229 (p : Pattern) (guard : walkGuard soko3_2.board support p 278 279 .east = true) : bonus 278 p ≤ bonus 279 p := by
  have certified := compare0 p (guard1229 p guard)
  simpa only [at278, at279, Int.zero_add] using certified
theorem check1229 (p : Pattern) : (!walkGuard soko3_2.board support p 278 279 .east || decide (bonus 278 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound1229 p)
theorem guard1230 (p : Pattern) (guard : pushGuard support p 278 279 280 280 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1230 (p : Pattern) (guard : pushGuard support p 278 279 280 280 = true) : bonus 278 p ≤ 1 + Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.boulder 279 + bonus 279 (change p 279 (some 280)) := by
  have certified := compare104 p (guard1230 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 279 (some 280))
  have normalized := agree134 _ _ (change_representative support p 279 (some 280) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1230 (p : Pattern) : (!pushGuard support p 278 279 280 280 || decide (bonus 278 p ≤ 1 + Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.boulder 279 + bonus 279 (change p 279 (some 280)))) = true :=
  check_of_implication _ _ (bound1230 p)
theorem guard1231 (p : Pattern) (guard : pushGuard support p 278 279 280 280 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1231 (p : Pattern) (guard : pushGuard support p 278 279 280 280 = true) : bonus 278 p ≤ 1 - Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.hole 280 + bonus 279 (change p 279 none) := by
  have certified := compare104 p (guard1231 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 279 none)
  have normalized := agree134 _ _ (change_representative support p 279 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1231 (p : Pattern) : (!pushGuard support p 278 279 280 280 || decide (bonus 278 p ≤ 1 - Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.hole 280 + bonus 279 (change p 279 none))) = true :=
  check_of_implication _ _ (bound1231 p)
theorem guard1232 (p : Pattern) (guard : walkGuard soko3_2.board support p 278 277 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1232 (p : Pattern) (guard : walkGuard soko3_2.board support p 278 277 .west = true) : bonus 278 p ≤ bonus 277 p := by
  have certified := compare0 p (guard1232 p guard)
  simpa only [at278, at277, Int.zero_add] using certified
theorem check1232 (p : Pattern) : (!walkGuard soko3_2.board support p 278 277 .west || decide (bonus 278 p ≤ bonus 277 p)) = true :=
  check_of_implication _ _ (bound1232 p)
theorem guard1233 (p : Pattern) (guard : pushGuard support p 278 277 276 276 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1233 (p : Pattern) (guard : pushGuard support p 278 277 276 276 = true) : bonus 278 p ≤ 1 + Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.boulder 277 + bonus 277 (change p 277 (some 276)) := by
  have certified := compare104 p (guard1233 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 277 (some 276))
  have normalized := agree134 _ _ (change_representative support p 277 (some 276) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1233 (p : Pattern) : (!pushGuard support p 278 277 276 276 || decide (bonus 278 p ≤ 1 + Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.boulder 277 + bonus 277 (change p 277 (some 276)))) = true :=
  check_of_implication _ _ (bound1233 p)
theorem guard1234 (p : Pattern) (guard : pushGuard support p 278 277 276 276 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1234 (p : Pattern) (guard : pushGuard support p 278 277 276 276 = true) : bonus 278 p ≤ 1 - Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.hole 276 + bonus 277 (change p 277 none) := by
  have certified := compare104 p (guard1234 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 277 none)
  have normalized := agree134 _ _ (change_representative support p 277 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1234 (p : Pattern) : (!pushGuard support p 278 277 276 276 || decide (bonus 278 p ≤ 1 - Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.hole 276 + bonus 277 (change p 277 none))) = true :=
  check_of_implication _ _ (bound1234 p)
theorem guard1235 (p : Pattern) (guard : walkGuard soko3_2.board support p 279 280 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1235 (p : Pattern) (guard : walkGuard soko3_2.board support p 279 280 .east = true) : bonus 279 p ≤ bonus 280 p := by
  have certified := compare0 p (guard1235 p guard)
  simpa only [at279, at280, Int.zero_add] using certified
theorem check1235 (p : Pattern) : (!walkGuard soko3_2.board support p 279 280 .east || decide (bonus 279 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound1235 p)
theorem guard1236 (p : Pattern) (guard : pushGuard support p 279 280 281 281 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1236 (p : Pattern) (guard : pushGuard support p 279 280 281 281 = true) : bonus 279 p ≤ 1 + Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.boulder 280 + bonus 280 (change p 280 (some 281)) := by
  have certified := compare104 p (guard1236 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 280 (some 281))
  have normalized := agree134 _ _ (change_representative support p 280 (some 281) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1236 (p : Pattern) : (!pushGuard support p 279 280 281 281 || decide (bonus 279 p ≤ 1 + Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.boulder 280 + bonus 280 (change p 280 (some 281)))) = true :=
  check_of_implication _ _ (bound1236 p)
theorem guard1237 (p : Pattern) (guard : pushGuard support p 279 280 281 281 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1237 (p : Pattern) (guard : pushGuard support p 279 280 281 281 = true) : bonus 279 p ≤ 1 - Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.hole 281 + bonus 280 (change p 280 none) := by
  have certified := compare104 p (guard1237 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 280 none)
  have normalized := agree134 _ _ (change_representative support p 280 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1237 (p : Pattern) : (!pushGuard support p 279 280 281 281 || decide (bonus 279 p ≤ 1 - Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.hole 281 + bonus 280 (change p 280 none))) = true :=
  check_of_implication _ _ (bound1237 p)
theorem guard1238 (p : Pattern) (guard : walkGuard soko3_2.board support p 279 278 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1238 (p : Pattern) (guard : walkGuard soko3_2.board support p 279 278 .west = true) : bonus 279 p ≤ bonus 278 p := by
  have certified := compare0 p (guard1238 p guard)
  simpa only [at279, at278, Int.zero_add] using certified
theorem check1238 (p : Pattern) : (!walkGuard soko3_2.board support p 279 278 .west || decide (bonus 279 p ≤ bonus 278 p)) = true :=
  check_of_implication _ _ (bound1238 p)
theorem guard1239 (p : Pattern) (guard : pushGuard support p 279 278 277 277 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1239 (p : Pattern) (guard : pushGuard support p 279 278 277 277 = true) : bonus 279 p ≤ 1 + Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.boulder 278 + bonus 278 (change p 278 (some 277)) := by
  have certified := compare104 p (guard1239 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 278 (some 277))
  have normalized := agree134 _ _ (change_representative support p 278 (some 277) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1239 (p : Pattern) : (!pushGuard support p 279 278 277 277 || decide (bonus 279 p ≤ 1 + Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.boulder 278 + bonus 278 (change p 278 (some 277)))) = true :=
  check_of_implication _ _ (bound1239 p)
theorem guard1240 (p : Pattern) (guard : pushGuard support p 279 278 277 277 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1240 (p : Pattern) (guard : pushGuard support p 279 278 277 277 = true) : bonus 279 p ≤ 1 - Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.hole 277 + bonus 278 (change p 278 none) := by
  have certified := compare104 p (guard1240 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 278 none)
  have normalized := agree134 _ _ (change_representative support p 278 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1240 (p : Pattern) : (!pushGuard support p 279 278 277 277 || decide (bonus 279 p ≤ 1 - Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.hole 277 + bonus 278 (change p 278 none))) = true :=
  check_of_implication _ _ (bound1240 p)
theorem guard1241 (p : Pattern) (guard : walkGuard soko3_2.board support p 280 281 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1241 (p : Pattern) (guard : walkGuard soko3_2.board support p 280 281 .east = true) : bonus 280 p ≤ bonus 281 p := by
  have certified := compare0 p (guard1241 p guard)
  simpa only [at280, at281, Int.zero_add] using certified
theorem check1241 (p : Pattern) : (!walkGuard soko3_2.board support p 280 281 .east || decide (bonus 280 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound1241 p)
theorem guard1242 (p : Pattern) (guard : pushGuard support p 280 281 282 282 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1242 (p : Pattern) (guard : pushGuard support p 280 281 282 282 = true) : bonus 280 p ≤ 1 + Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.boulder 281 + bonus 281 (change p 281 (some 282)) := by
  have certified := compare104 p (guard1242 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 281 (some 282))
  have normalized := agree134 _ _ (change_representative support p 281 (some 282) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1242 (p : Pattern) : (!pushGuard support p 280 281 282 282 || decide (bonus 280 p ≤ 1 + Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.boulder 281 + bonus 281 (change p 281 (some 282)))) = true :=
  check_of_implication _ _ (bound1242 p)
theorem guard1243 (p : Pattern) (guard : pushGuard support p 280 281 282 282 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1243 (p : Pattern) (guard : pushGuard support p 280 281 282 282 = true) : bonus 280 p ≤ 1 - Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.hole 282 + bonus 281 (change p 281 none) := by
  have certified := compare104 p (guard1243 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 281 none)
  have normalized := agree134 _ _ (change_representative support p 281 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1243 (p : Pattern) : (!pushGuard support p 280 281 282 282 || decide (bonus 280 p ≤ 1 - Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.hole 282 + bonus 281 (change p 281 none))) = true :=
  check_of_implication _ _ (bound1243 p)
theorem guard1244 (p : Pattern) (guard : walkGuard soko3_2.board support p 280 279 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1244 (p : Pattern) (guard : walkGuard soko3_2.board support p 280 279 .west = true) : bonus 280 p ≤ bonus 279 p := by
  have certified := compare0 p (guard1244 p guard)
  simpa only [at280, at279, Int.zero_add] using certified
theorem check1244 (p : Pattern) : (!walkGuard soko3_2.board support p 280 279 .west || decide (bonus 280 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound1244 p)
theorem guard1245 (p : Pattern) (guard : pushGuard support p 280 279 278 278 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1245 (p : Pattern) (guard : pushGuard support p 280 279 278 278 = true) : bonus 280 p ≤ 1 + Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.boulder 279 + bonus 279 (change p 279 (some 278)) := by
  have certified := compare104 p (guard1245 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 279 (some 278))
  have normalized := agree134 _ _ (change_representative support p 279 (some 278) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1245 (p : Pattern) : (!pushGuard support p 280 279 278 278 || decide (bonus 280 p ≤ 1 + Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.boulder 279 + bonus 279 (change p 279 (some 278)))) = true :=
  check_of_implication _ _ (bound1245 p)
theorem guard1246 (p : Pattern) (guard : pushGuard support p 280 279 278 278 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1246 (p : Pattern) (guard : pushGuard support p 280 279 278 278 = true) : bonus 280 p ≤ 1 - Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.hole 278 + bonus 279 (change p 279 none) := by
  have certified := compare104 p (guard1246 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 279 none)
  have normalized := agree134 _ _ (change_representative support p 279 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1246 (p : Pattern) : (!pushGuard support p 280 279 278 278 || decide (bonus 280 p ≤ 1 - Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.hole 278 + bonus 279 (change p 279 none))) = true :=
  check_of_implication _ _ (bound1246 p)
theorem guard1247 (p : Pattern) (guard : walkGuard soko3_2.board support p 281 282 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1247 (p : Pattern) (guard : walkGuard soko3_2.board support p 281 282 .east = true) : bonus 281 p ≤ bonus 282 p := by
  have certified := compare0 p (guard1247 p guard)
  simpa only [at281, at282, Int.zero_add] using certified
theorem check1247 (p : Pattern) : (!walkGuard soko3_2.board support p 281 282 .east || decide (bonus 281 p ≤ bonus 282 p)) = true :=
  check_of_implication _ _ (bound1247 p)
end NetHack.Sokoban32Refined
