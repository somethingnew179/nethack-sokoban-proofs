import NetHack.Sokoban32Refined.ActionBounds049
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1200 (p : Pattern) (guard : pushGuard support p 273 274 275 275 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1200 (p : Pattern) (guard : pushGuard support p 273 274 275 275 = true) : bonus 273 p ≤ 1 + Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.boulder 274 + bonus 274 (change p 274 (some 275)) := by
  have certified := compare104 p (guard1200 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 274 (some 275))
  have normalized := agree134 _ _ (change_representative support p 274 (some 275) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1200 (p : Pattern) : (!pushGuard support p 273 274 275 275 || decide (bonus 273 p ≤ 1 + Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.boulder 274 + bonus 274 (change p 274 (some 275)))) = true :=
  check_of_implication _ _ (bound1200 p)
theorem guard1201 (p : Pattern) (guard : pushGuard support p 273 274 275 275 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1201 (p : Pattern) (guard : pushGuard support p 273 274 275 275 = true) : bonus 273 p ≤ 1 - Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.hole 275 + bonus 274 (change p 274 none) := by
  have certified := compare104 p (guard1201 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 274 none)
  have normalized := agree134 _ _ (change_representative support p 274 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1201 (p : Pattern) : (!pushGuard support p 273 274 275 275 || decide (bonus 273 p ≤ 1 - Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.hole 275 + bonus 274 (change p 274 none))) = true :=
  check_of_implication _ _ (bound1201 p)
theorem guard1202 (p : Pattern) (guard : walkGuard soko3_2.board support p 273 272 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1202 (p : Pattern) (guard : walkGuard soko3_2.board support p 273 272 .west = true) : bonus 273 p ≤ bonus 272 p := by
  have certified := compare0 p (guard1202 p guard)
  simpa only [at273, at272, Int.zero_add] using certified
theorem check1202 (p : Pattern) : (!walkGuard soko3_2.board support p 273 272 .west || decide (bonus 273 p ≤ bonus 272 p)) = true :=
  check_of_implication _ _ (bound1202 p)
theorem guard1203 (p : Pattern) (guard : pushGuard support p 273 272 271 269 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1203 (p : Pattern) (guard : pushGuard support p 273 272 271 269 = true) : bonus 273 p ≤ 1 + Generated.soko3_2Potential.boulder 269 - Generated.soko3_2Potential.boulder 272 + bonus 272 (change p 272 (some 269)) := by
  have certified := compare8906 p (guard1203 p guard)
  change d134 p ≤ (5 : Int) + d134 (change p 272 (some 269))
  have normalized := agree134 _ _ (change_representative support p 272 (some 269) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (5 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1203 (p : Pattern) : (!pushGuard support p 273 272 271 269 || decide (bonus 273 p ≤ 1 + Generated.soko3_2Potential.boulder 269 - Generated.soko3_2Potential.boulder 272 + bonus 272 (change p 272 (some 269)))) = true :=
  check_of_implication _ _ (bound1203 p)
theorem guard1204 (p : Pattern) (guard : pushGuard support p 273 272 271 272 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1204 (p : Pattern) (guard : pushGuard support p 273 272 271 272 = true) : bonus 273 p ≤ 1 - Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.hole 272 + bonus 272 (change p 272 none) := by
  have certified := compare104 p (guard1204 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 272 none)
  have normalized := agree134 _ _ (change_representative support p 272 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1204 (p : Pattern) : (!pushGuard support p 273 272 271 272 || decide (bonus 273 p ≤ 1 - Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.hole 272 + bonus 272 (change p 272 none))) = true :=
  check_of_implication _ _ (bound1204 p)
theorem guard1205 (p : Pattern) (guard : walkGuard soko3_2.board support p 274 275 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1205 (p : Pattern) (guard : walkGuard soko3_2.board support p 274 275 .east = true) : bonus 274 p ≤ bonus 275 p := by
  have certified := compare0 p (guard1205 p guard)
  simpa only [at274, at275, Int.zero_add] using certified
theorem check1205 (p : Pattern) : (!walkGuard soko3_2.board support p 274 275 .east || decide (bonus 274 p ≤ bonus 275 p)) = true :=
  check_of_implication _ _ (bound1205 p)
theorem guard1206 (p : Pattern) (guard : pushGuard support p 274 275 276 276 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1206 (p : Pattern) (guard : pushGuard support p 274 275 276 276 = true) : bonus 274 p ≤ 1 + Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.boulder 275 + bonus 275 (change p 275 (some 276)) := by
  have certified := compare104 p (guard1206 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 275 (some 276))
  have normalized := agree134 _ _ (change_representative support p 275 (some 276) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1206 (p : Pattern) : (!pushGuard support p 274 275 276 276 || decide (bonus 274 p ≤ 1 + Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.boulder 275 + bonus 275 (change p 275 (some 276)))) = true :=
  check_of_implication _ _ (bound1206 p)
theorem guard1207 (p : Pattern) (guard : pushGuard support p 274 275 276 276 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1207 (p : Pattern) (guard : pushGuard support p 274 275 276 276 = true) : bonus 274 p ≤ 1 - Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.hole 276 + bonus 275 (change p 275 none) := by
  have certified := compare104 p (guard1207 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 275 none)
  have normalized := agree134 _ _ (change_representative support p 275 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1207 (p : Pattern) : (!pushGuard support p 274 275 276 276 || decide (bonus 274 p ≤ 1 - Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.hole 276 + bonus 275 (change p 275 none))) = true :=
  check_of_implication _ _ (bound1207 p)
theorem guard1208 (p : Pattern) (guard : walkGuard soko3_2.board support p 274 273 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1208 (p : Pattern) (guard : walkGuard soko3_2.board support p 274 273 .west = true) : bonus 274 p ≤ bonus 273 p := by
  have certified := compare0 p (guard1208 p guard)
  simpa only [at274, at273, Int.zero_add] using certified
theorem check1208 (p : Pattern) : (!walkGuard soko3_2.board support p 274 273 .west || decide (bonus 274 p ≤ bonus 273 p)) = true :=
  check_of_implication _ _ (bound1208 p)
theorem guard1209 (p : Pattern) (guard : pushGuard support p 274 273 272 272 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1209 (p : Pattern) (guard : pushGuard support p 274 273 272 272 = true) : bonus 274 p ≤ 1 + Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.boulder 273 + bonus 273 (change p 273 (some 272)) := by
  have certified := compare104 p (guard1209 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 273 (some 272))
  have normalized := agree134 _ _ (change_representative support p 273 (some 272) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1209 (p : Pattern) : (!pushGuard support p 274 273 272 272 || decide (bonus 274 p ≤ 1 + Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.boulder 273 + bonus 273 (change p 273 (some 272)))) = true :=
  check_of_implication _ _ (bound1209 p)
theorem guard1210 (p : Pattern) (guard : pushGuard support p 274 273 272 272 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1210 (p : Pattern) (guard : pushGuard support p 274 273 272 272 = true) : bonus 274 p ≤ 1 - Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.hole 272 + bonus 273 (change p 273 none) := by
  have certified := compare104 p (guard1210 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 273 none)
  have normalized := agree134 _ _ (change_representative support p 273 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1210 (p : Pattern) : (!pushGuard support p 274 273 272 272 || decide (bonus 274 p ≤ 1 - Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.hole 272 + bonus 273 (change p 273 none))) = true :=
  check_of_implication _ _ (bound1210 p)
theorem guard1211 (p : Pattern) (guard : walkGuard soko3_2.board support p 275 276 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1211 (p : Pattern) (guard : walkGuard soko3_2.board support p 275 276 .east = true) : bonus 275 p ≤ bonus 276 p := by
  have certified := compare0 p (guard1211 p guard)
  simpa only [at275, at276, Int.zero_add] using certified
theorem check1211 (p : Pattern) : (!walkGuard soko3_2.board support p 275 276 .east || decide (bonus 275 p ≤ bonus 276 p)) = true :=
  check_of_implication _ _ (bound1211 p)
theorem guard1212 (p : Pattern) (guard : pushGuard support p 275 276 277 277 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1212 (p : Pattern) (guard : pushGuard support p 275 276 277 277 = true) : bonus 275 p ≤ 1 + Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.boulder 276 + bonus 276 (change p 276 (some 277)) := by
  have certified := compare104 p (guard1212 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 276 (some 277))
  have normalized := agree134 _ _ (change_representative support p 276 (some 277) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1212 (p : Pattern) : (!pushGuard support p 275 276 277 277 || decide (bonus 275 p ≤ 1 + Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.boulder 276 + bonus 276 (change p 276 (some 277)))) = true :=
  check_of_implication _ _ (bound1212 p)
theorem guard1213 (p : Pattern) (guard : pushGuard support p 275 276 277 277 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1213 (p : Pattern) (guard : pushGuard support p 275 276 277 277 = true) : bonus 275 p ≤ 1 - Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.hole 277 + bonus 276 (change p 276 none) := by
  have certified := compare104 p (guard1213 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 276 none)
  have normalized := agree134 _ _ (change_representative support p 276 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1213 (p : Pattern) : (!pushGuard support p 275 276 277 277 || decide (bonus 275 p ≤ 1 - Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.hole 277 + bonus 276 (change p 276 none))) = true :=
  check_of_implication _ _ (bound1213 p)
theorem guard1214 (p : Pattern) (guard : walkGuard soko3_2.board support p 275 274 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1214 (p : Pattern) (guard : walkGuard soko3_2.board support p 275 274 .west = true) : bonus 275 p ≤ bonus 274 p := by
  have certified := compare0 p (guard1214 p guard)
  simpa only [at275, at274, Int.zero_add] using certified
theorem check1214 (p : Pattern) : (!walkGuard soko3_2.board support p 275 274 .west || decide (bonus 275 p ≤ bonus 274 p)) = true :=
  check_of_implication _ _ (bound1214 p)
theorem guard1215 (p : Pattern) (guard : pushGuard support p 275 274 273 273 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1215 (p : Pattern) (guard : pushGuard support p 275 274 273 273 = true) : bonus 275 p ≤ 1 + Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.boulder 274 + bonus 274 (change p 274 (some 273)) := by
  have certified := compare104 p (guard1215 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 274 (some 273))
  have normalized := agree134 _ _ (change_representative support p 274 (some 273) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1215 (p : Pattern) : (!pushGuard support p 275 274 273 273 || decide (bonus 275 p ≤ 1 + Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.boulder 274 + bonus 274 (change p 274 (some 273)))) = true :=
  check_of_implication _ _ (bound1215 p)
theorem guard1216 (p : Pattern) (guard : pushGuard support p 275 274 273 273 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1216 (p : Pattern) (guard : pushGuard support p 275 274 273 273 = true) : bonus 275 p ≤ 1 - Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.hole 273 + bonus 274 (change p 274 none) := by
  have certified := compare104 p (guard1216 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 274 none)
  have normalized := agree134 _ _ (change_representative support p 274 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1216 (p : Pattern) : (!pushGuard support p 275 274 273 273 || decide (bonus 275 p ≤ 1 - Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.hole 273 + bonus 274 (change p 274 none))) = true :=
  check_of_implication _ _ (bound1216 p)
theorem guard1217 (p : Pattern) (guard : walkGuard soko3_2.board support p 276 277 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1217 (p : Pattern) (guard : walkGuard soko3_2.board support p 276 277 .east = true) : bonus 276 p ≤ bonus 277 p := by
  have certified := compare0 p (guard1217 p guard)
  simpa only [at276, at277, Int.zero_add] using certified
theorem check1217 (p : Pattern) : (!walkGuard soko3_2.board support p 276 277 .east || decide (bonus 276 p ≤ bonus 277 p)) = true :=
  check_of_implication _ _ (bound1217 p)
theorem guard1218 (p : Pattern) (guard : pushGuard support p 276 277 278 278 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1218 (p : Pattern) (guard : pushGuard support p 276 277 278 278 = true) : bonus 276 p ≤ 1 + Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.boulder 277 + bonus 277 (change p 277 (some 278)) := by
  have certified := compare104 p (guard1218 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 277 (some 278))
  have normalized := agree134 _ _ (change_representative support p 277 (some 278) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1218 (p : Pattern) : (!pushGuard support p 276 277 278 278 || decide (bonus 276 p ≤ 1 + Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.boulder 277 + bonus 277 (change p 277 (some 278)))) = true :=
  check_of_implication _ _ (bound1218 p)
theorem guard1219 (p : Pattern) (guard : pushGuard support p 276 277 278 278 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1219 (p : Pattern) (guard : pushGuard support p 276 277 278 278 = true) : bonus 276 p ≤ 1 - Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.hole 278 + bonus 277 (change p 277 none) := by
  have certified := compare104 p (guard1219 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 277 none)
  have normalized := agree134 _ _ (change_representative support p 277 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1219 (p : Pattern) : (!pushGuard support p 276 277 278 278 || decide (bonus 276 p ≤ 1 - Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.hole 278 + bonus 277 (change p 277 none))) = true :=
  check_of_implication _ _ (bound1219 p)
theorem guard1220 (p : Pattern) (guard : walkGuard soko3_2.board support p 276 275 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1220 (p : Pattern) (guard : walkGuard soko3_2.board support p 276 275 .west = true) : bonus 276 p ≤ bonus 275 p := by
  have certified := compare0 p (guard1220 p guard)
  simpa only [at276, at275, Int.zero_add] using certified
theorem check1220 (p : Pattern) : (!walkGuard soko3_2.board support p 276 275 .west || decide (bonus 276 p ≤ bonus 275 p)) = true :=
  check_of_implication _ _ (bound1220 p)
theorem guard1221 (p : Pattern) (guard : pushGuard support p 276 275 274 274 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1221 (p : Pattern) (guard : pushGuard support p 276 275 274 274 = true) : bonus 276 p ≤ 1 + Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.boulder 275 + bonus 275 (change p 275 (some 274)) := by
  have certified := compare104 p (guard1221 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 275 (some 274))
  have normalized := agree134 _ _ (change_representative support p 275 (some 274) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1221 (p : Pattern) : (!pushGuard support p 276 275 274 274 || decide (bonus 276 p ≤ 1 + Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.boulder 275 + bonus 275 (change p 275 (some 274)))) = true :=
  check_of_implication _ _ (bound1221 p)
theorem guard1222 (p : Pattern) (guard : pushGuard support p 276 275 274 274 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1222 (p : Pattern) (guard : pushGuard support p 276 275 274 274 = true) : bonus 276 p ≤ 1 - Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.hole 274 + bonus 275 (change p 275 none) := by
  have certified := compare104 p (guard1222 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 275 none)
  have normalized := agree134 _ _ (change_representative support p 275 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1222 (p : Pattern) : (!pushGuard support p 276 275 274 274 || decide (bonus 276 p ≤ 1 - Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.hole 274 + bonus 275 (change p 275 none))) = true :=
  check_of_implication _ _ (bound1222 p)
theorem guard1223 (p : Pattern) (guard : walkGuard soko3_2.board support p 277 278 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1223 (p : Pattern) (guard : walkGuard soko3_2.board support p 277 278 .east = true) : bonus 277 p ≤ bonus 278 p := by
  have certified := compare0 p (guard1223 p guard)
  simpa only [at277, at278, Int.zero_add] using certified
theorem check1223 (p : Pattern) : (!walkGuard soko3_2.board support p 277 278 .east || decide (bonus 277 p ≤ bonus 278 p)) = true :=
  check_of_implication _ _ (bound1223 p)
end NetHack.Sokoban32Refined
