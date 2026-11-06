import NetHack.Sokoban32Refined.ActionBounds048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1176 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 294 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1176 (p : Pattern) (guard : walkGuard soko3_2.board support p 269 294 .southWest = true) : bonus 269 p ≤ bonus 294 p := by
  have certified := compare0 p (guard1176 p guard)
  simpa only [at269, at294, Int.zero_add] using certified
theorem check1176 (p : Pattern) : (!walkGuard soko3_2.board support p 269 294 .southWest || decide (bonus 269 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound1176 p)
theorem guard1177 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 244 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1177 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 244 .north = true) : bonus 270 p ≤ bonus 244 p := by
  have certified := compare0 p (guard1177 p guard)
  simpa only [at270, at244, Int.zero_add] using certified
theorem check1177 (p : Pattern) : (!walkGuard soko3_2.board support p 270 244 .north || decide (bonus 270 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound1177 p)
theorem guard1178 (p : Pattern) (guard : pushGuard support p 270 244 218 218 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1178 (p : Pattern) (guard : pushGuard support p 270 244 218 218 = true) : bonus 270 p ≤ 1 + Generated.soko3_2Potential.boulder 218 - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some 218)) := by
  have certified := compare4301 p (guard1178 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 244 (some 218))
  have normalized := agree134 _ _ (change_representative support p 244 (some 218) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1178 (p : Pattern) : (!pushGuard support p 270 244 218 218 || decide (bonus 270 p ≤ 1 + Generated.soko3_2Potential.boulder 218 - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some 218)))) = true :=
  check_of_implication _ _ (bound1178 p)
theorem guard1179 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 271 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1179 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 271 .east = true) : bonus 270 p ≤ bonus 271 p := by
  have certified := compare0 p (guard1179 p guard)
  simpa only [at270, at271, Int.zero_add] using certified
theorem check1179 (p : Pattern) : (!walkGuard soko3_2.board support p 270 271 .east || decide (bonus 270 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound1179 p)
theorem guard1180 (p : Pattern) (guard : pushGuard support p 270 271 272 272 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1180 (p : Pattern) (guard : pushGuard support p 270 271 272 272 = true) : bonus 270 p ≤ 1 + Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.boulder 271 + bonus 271 (change p 271 (some 272)) := by
  have certified := compare0 p (guard1180 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 271 (some 272))
  have normalized := agree134 _ _ (change_representative support p 271 (some 272) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1180 (p : Pattern) : (!pushGuard support p 270 271 272 272 || decide (bonus 270 p ≤ 1 + Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.boulder 271 + bonus 271 (change p 271 (some 272)))) = true :=
  check_of_implication _ _ (bound1180 p)
theorem guard1181 (p : Pattern) (guard : pushGuard support p 270 271 272 272 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1181 (p : Pattern) (guard : pushGuard support p 270 271 272 272 = true) : bonus 270 p ≤ 1 - Generated.soko3_2Potential.boulder 271 - Generated.soko3_2Potential.hole 272 + bonus 271 (change p 271 none) := by
  have certified := compare0 p (guard1181 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 271 none)
  have normalized := agree134 _ _ (change_representative support p 271 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1181 (p : Pattern) : (!pushGuard support p 270 271 272 272 || decide (bonus 270 p ≤ 1 - Generated.soko3_2Potential.boulder 271 - Generated.soko3_2Potential.hole 272 + bonus 271 (change p 271 none))) = true :=
  check_of_implication _ _ (bound1181 p)
theorem guard1182 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 269 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1182 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 269 .west = true) : bonus 270 p ≤ bonus 269 p := by
  have certified := compare0 p (guard1182 p guard)
  simpa only [at270, at269, Int.zero_add] using certified
theorem check1182 (p : Pattern) : (!walkGuard soko3_2.board support p 270 269 .west || decide (bonus 270 p ≤ bonus 269 p)) = true :=
  check_of_implication _ _ (bound1182 p)
theorem guard1183 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 245 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1183 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 245 .northEast = true) : bonus 270 p ≤ bonus 245 p := by
  have certified := compare0 p (guard1183 p guard)
  simpa only [at270, at245, Int.zero_add] using certified
theorem check1183 (p : Pattern) : (!walkGuard soko3_2.board support p 270 245 .northEast || decide (bonus 270 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound1183 p)
theorem guard1184 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 243 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1184 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 243 .northWest = true) : bonus 270 p ≤ bonus 243 p := by
  have certified := compare0 p (guard1184 p guard)
  simpa only [at270, at243, Int.zero_add] using certified
theorem check1184 (p : Pattern) : (!walkGuard soko3_2.board support p 270 243 .northWest || decide (bonus 270 p ≤ bonus 243 p)) = true :=
  check_of_implication _ _ (bound1184 p)
theorem guard1185 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 295 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1185 (p : Pattern) (guard : walkGuard soko3_2.board support p 270 295 .southWest = true) : bonus 270 p ≤ bonus 295 p := by
  have certified := compare0 p (guard1185 p guard)
  simpa only [at270, at295, Int.zero_add] using certified
theorem check1185 (p : Pattern) : (!walkGuard soko3_2.board support p 270 295 .southWest || decide (bonus 270 p ≤ bonus 295 p)) = true :=
  check_of_implication _ _ (bound1185 p)
theorem guard1186 (p : Pattern) (guard : walkGuard soko3_2.board support p 271 245 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1186 (p : Pattern) (guard : walkGuard soko3_2.board support p 271 245 .north = true) : bonus 271 p ≤ bonus 245 p := by
  have certified := compare0 p (guard1186 p guard)
  simpa only [at271, at245, Int.zero_add] using certified
theorem check1186 (p : Pattern) : (!walkGuard soko3_2.board support p 271 245 .north || decide (bonus 271 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound1186 p)
theorem guard1187 (p : Pattern) (guard : walkGuard soko3_2.board support p 271 272 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1187 (p : Pattern) (guard : walkGuard soko3_2.board support p 271 272 .east = true) : bonus 271 p ≤ bonus 272 p := by
  have certified := compare0 p (guard1187 p guard)
  simpa only [at271, at272, Int.zero_add] using certified
theorem check1187 (p : Pattern) : (!walkGuard soko3_2.board support p 271 272 .east || decide (bonus 271 p ≤ bonus 272 p)) = true :=
  check_of_implication _ _ (bound1187 p)
theorem guard1188 (p : Pattern) (guard : pushGuard support p 271 272 273 273 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1188 (p : Pattern) (guard : pushGuard support p 271 272 273 273 = true) : bonus 271 p ≤ 1 + Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.boulder 272 + bonus 272 (change p 272 (some 273)) := by
  have certified := compare104 p (guard1188 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 272 (some 273))
  have normalized := agree134 _ _ (change_representative support p 272 (some 273) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1188 (p : Pattern) : (!pushGuard support p 271 272 273 273 || decide (bonus 271 p ≤ 1 + Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.boulder 272 + bonus 272 (change p 272 (some 273)))) = true :=
  check_of_implication _ _ (bound1188 p)
theorem guard1189 (p : Pattern) (guard : pushGuard support p 271 272 273 273 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1189 (p : Pattern) (guard : pushGuard support p 271 272 273 273 = true) : bonus 271 p ≤ 1 - Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.hole 273 + bonus 272 (change p 272 none) := by
  have certified := compare104 p (guard1189 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 272 none)
  have normalized := agree134 _ _ (change_representative support p 272 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1189 (p : Pattern) : (!pushGuard support p 271 272 273 273 || decide (bonus 271 p ≤ 1 - Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.hole 273 + bonus 272 (change p 272 none))) = true :=
  check_of_implication _ _ (bound1189 p)
theorem guard1190 (p : Pattern) (guard : walkGuard soko3_2.board support p 271 270 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1190 (p : Pattern) (guard : walkGuard soko3_2.board support p 271 270 .west = true) : bonus 271 p ≤ bonus 270 p := by
  have certified := compare0 p (guard1190 p guard)
  simpa only [at271, at270, Int.zero_add] using certified
theorem check1190 (p : Pattern) : (!walkGuard soko3_2.board support p 271 270 .west || decide (bonus 271 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound1190 p)
theorem guard1191 (p : Pattern) (guard : pushGuard support p 271 270 269 269 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1191 (p : Pattern) (guard : pushGuard support p 271 270 269 269 = true) : bonus 271 p ≤ 1 + Generated.soko3_2Potential.boulder 269 - Generated.soko3_2Potential.boulder 270 + bonus 270 (change p 270 (some 269)) := by
  have certified := compare9360 p (guard1191 p guard)
  change d134 p ≤ (4 : Int) + d134 (change p 270 (some 269))
  have normalized := agree134 _ _ (change_representative support p 270 (some 269) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (4 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1191 (p : Pattern) : (!pushGuard support p 271 270 269 269 || decide (bonus 271 p ≤ 1 + Generated.soko3_2Potential.boulder 269 - Generated.soko3_2Potential.boulder 270 + bonus 270 (change p 270 (some 269)))) = true :=
  check_of_implication _ _ (bound1191 p)
theorem guard1192 (p : Pattern) (guard : walkGuard soko3_2.board support p 271 244 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1192 (p : Pattern) (guard : walkGuard soko3_2.board support p 271 244 .northWest = true) : bonus 271 p ≤ bonus 244 p := by
  have certified := compare0 p (guard1192 p guard)
  simpa only [at271, at244, Int.zero_add] using certified
theorem check1192 (p : Pattern) : (!walkGuard soko3_2.board support p 271 244 .northWest || decide (bonus 271 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound1192 p)
theorem guard1193 (p : Pattern) (guard : walkGuard soko3_2.board support p 272 273 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1193 (p : Pattern) (guard : walkGuard soko3_2.board support p 272 273 .east = true) : bonus 272 p ≤ bonus 273 p := by
  have certified := compare0 p (guard1193 p guard)
  simpa only [at272, at273, Int.zero_add] using certified
theorem check1193 (p : Pattern) : (!walkGuard soko3_2.board support p 272 273 .east || decide (bonus 272 p ≤ bonus 273 p)) = true :=
  check_of_implication _ _ (bound1193 p)
theorem guard1194 (p : Pattern) (guard : pushGuard support p 272 273 274 274 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1194 (p : Pattern) (guard : pushGuard support p 272 273 274 274 = true) : bonus 272 p ≤ 1 + Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.boulder 273 + bonus 273 (change p 273 (some 274)) := by
  have certified := compare104 p (guard1194 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 273 (some 274))
  have normalized := agree134 _ _ (change_representative support p 273 (some 274) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1194 (p : Pattern) : (!pushGuard support p 272 273 274 274 || decide (bonus 272 p ≤ 1 + Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.boulder 273 + bonus 273 (change p 273 (some 274)))) = true :=
  check_of_implication _ _ (bound1194 p)
theorem guard1195 (p : Pattern) (guard : pushGuard support p 272 273 274 274 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1195 (p : Pattern) (guard : pushGuard support p 272 273 274 274 = true) : bonus 272 p ≤ 1 - Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.hole 274 + bonus 273 (change p 273 none) := by
  have certified := compare104 p (guard1195 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 273 none)
  have normalized := agree134 _ _ (change_representative support p 273 none 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1195 (p : Pattern) : (!pushGuard support p 272 273 274 274 || decide (bonus 272 p ≤ 1 - Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.hole 274 + bonus 273 (change p 273 none))) = true :=
  check_of_implication _ _ (bound1195 p)
theorem guard1196 (p : Pattern) (guard : walkGuard soko3_2.board support p 272 271 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1196 (p : Pattern) (guard : walkGuard soko3_2.board support p 272 271 .west = true) : bonus 272 p ≤ bonus 271 p := by
  have certified := compare0 p (guard1196 p guard)
  simpa only [at272, at271, Int.zero_add] using certified
theorem check1196 (p : Pattern) : (!walkGuard soko3_2.board support p 272 271 .west || decide (bonus 272 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound1196 p)
theorem guard1197 (p : Pattern) (guard : pushGuard support p 272 271 270 270 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1197 (p : Pattern) (guard : pushGuard support p 272 271 270 270 = true) : bonus 272 p ≤ 1 + Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.boulder 271 + bonus 271 (change p 271 (some 270)) := by
  have certified := compare104 p (guard1197 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 271 (some 270))
  have normalized := agree134 _ _ (change_representative support p 271 (some 270) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1197 (p : Pattern) : (!pushGuard support p 272 271 270 270 || decide (bonus 272 p ≤ 1 + Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.boulder 271 + bonus 271 (change p 271 (some 270)))) = true :=
  check_of_implication _ _ (bound1197 p)
theorem guard1198 (p : Pattern) (guard : walkGuard soko3_2.board support p 272 245 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1198 (p : Pattern) (guard : walkGuard soko3_2.board support p 272 245 .northWest = true) : bonus 272 p ≤ bonus 245 p := by
  have certified := compare0 p (guard1198 p guard)
  simpa only [at272, at245, Int.zero_add] using certified
theorem check1198 (p : Pattern) : (!walkGuard soko3_2.board support p 272 245 .northWest || decide (bonus 272 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound1198 p)
theorem guard1199 (p : Pattern) (guard : walkGuard soko3_2.board support p 273 274 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1199 (p : Pattern) (guard : walkGuard soko3_2.board support p 273 274 .east = true) : bonus 273 p ≤ bonus 274 p := by
  have certified := compare0 p (guard1199 p guard)
  simpa only [at273, at274, Int.zero_add] using certified
theorem check1199 (p : Pattern) : (!walkGuard soko3_2.board support p 273 274 .east || decide (bonus 273 p ≤ bonus 274 p)) = true :=
  check_of_implication _ _ (bound1199 p)
end NetHack.Sokoban32Refined
