import NetHack.Sokoban12CostPartition.ActionBounds022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard552 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 246 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound552 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 246 .southEast = true) : bonus 219 p ≤ bonus 246 p := by
  have certified := compare897 p (guard552 p guard)
  simpa only [at219, at246, Int.zero_add] using certified
theorem check552 (p : Pattern) : (!walkGuard soko1_2.board support p 219 246 .southEast || decide (bonus 219 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound552 p)
theorem guard553 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 244 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound553 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 244 .southWest = true) : bonus 219 p ≤ bonus 244 p := by
  have certified := compare897 p (guard553 p guard)
  simpa only [at219, at244, Int.zero_add] using certified
theorem check553 (p : Pattern) : (!walkGuard soko1_2.board support p 219 244 .southWest || decide (bonus 219 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound553 p)
theorem guard554 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 194 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound554 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 194 .north = true) : bonus 220 p ≤ bonus 194 p := by
  have certified := compare897 p (guard554 p guard)
  simpa only [at220, at194, Int.zero_add] using certified
theorem check554 (p : Pattern) : (!walkGuard soko1_2.board support p 220 194 .north || decide (bonus 220 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound554 p)
theorem guard555 (p : Pattern) (guard : pushGuard support p 220 194 168 168 = true) : d770 p = 1 := by
  change (!false && (!false || false) && !(p 168) && (!(p 168) || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound555 (p : Pattern) (guard : pushGuard support p 220 194 168 168 = true) : bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.boulder 194 + bonus 194 (change p 194 (some 168)) := by
  have certified := compare5923 p (guard555 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 194 (some 168))
  have normalized := agree258 _ _ (change_representative support p 194 (some 168) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 (some 168))
  rw [sub1676]
  exact certified
theorem check555 (p : Pattern) : (!pushGuard support p 220 194 168 168 || decide (bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.boulder 194 + bonus 194 (change p 194 (some 168)))) = true :=
  check_of_implication _ _ (bound555 p)
theorem guard556 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 246 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound556 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 246 .south = true) : bonus 220 p ≤ bonus 246 p := by
  have certified := compare897 p (guard556 p guard)
  simpa only [at220, at246, Int.zero_add] using certified
theorem check556 (p : Pattern) : (!walkGuard soko1_2.board support p 220 246 .south || decide (bonus 220 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound556 p)
theorem guard557 (p : Pattern) (guard : pushGuard support p 220 246 272 272 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound557 (p : Pattern) (guard : pushGuard support p 220 246 272 272 = true) : bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder 272 - Generated.soko1_2Potential.boulder 246 + bonus 246 (change p 246 (some 272)) := by
  have certified := compare5431 p (guard557 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 246 (some 272))
  have normalized := agree258 _ _ (change_representative support p 246 (some 272) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check557 (p : Pattern) : (!pushGuard support p 220 246 272 272 || decide (bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder 272 - Generated.soko1_2Potential.boulder 246 + bonus 246 (change p 246 (some 272)))) = true :=
  check_of_implication _ _ (bound557 p)
theorem guard558 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 219 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound558 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 219 .west = true) : bonus 220 p ≤ bonus 219 p := by
  have certified := compare897 p (guard558 p guard)
  simpa only [at220, at219, Int.zero_add] using certified
theorem check558 (p : Pattern) : (!walkGuard soko1_2.board support p 220 219 .west || decide (bonus 220 p ≤ bonus 219 p)) = true :=
  check_of_implication _ _ (bound558 p)
theorem guard559 (p : Pattern) (guard : pushGuard support p 220 219 218 218 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound559 (p : Pattern) (guard : pushGuard support p 220 219 218 218 = true) : bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder 218 - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some 218)) := by
  have certified := compare897 p (guard559 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 219 (some 218))
  have normalized := agree258 _ _ (change_representative support p 219 (some 218) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check559 (p : Pattern) : (!pushGuard support p 220 219 218 218 || decide (bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder 218 - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some 218)))) = true :=
  check_of_implication _ _ (bound559 p)
theorem guard560 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 193 .northWest = true) : d917 p = 1 := by
  change (!false && !(p 193) && !(true && false && false)) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound560 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 193 .northWest = true) : bonus 220 p ≤ bonus 193 p := by
  have certified := compare2879 p (guard560 p guard)
  simpa only [at220, at193, Int.zero_add] using certified
theorem check560 (p : Pattern) : (!walkGuard soko1_2.board support p 220 193 .northWest || decide (bonus 220 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound560 p)
theorem guard561 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 245 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound561 (p : Pattern) (guard : walkGuard soko1_2.board support p 220 245 .southWest = true) : bonus 220 p ≤ bonus 245 p := by
  have certified := compare897 p (guard561 p guard)
  simpa only [at220, at245, Int.zero_add] using certified
theorem check561 (p : Pattern) : (!walkGuard soko1_2.board support p 220 245 .southWest || decide (bonus 220 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound561 p)
theorem guard562 (p : Pattern) (guard : walkGuard soko1_2.board support p 232 206 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound562 (p : Pattern) (guard : walkGuard soko1_2.board support p 232 206 .north = true) : bonus 232 p ≤ bonus 206 p := by
  have certified := compare0 p (guard562 p guard)
  simpa only [at232, at206, Int.zero_add] using certified
theorem check562 (p : Pattern) : (!walkGuard soko1_2.board support p 232 206 .north || decide (bonus 232 p ≤ bonus 206 p)) = true :=
  check_of_implication _ _ (bound562 p)
theorem guard563 (p : Pattern) (guard : pushGuard support p 232 206 180 180 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound563 (p : Pattern) (guard : pushGuard support p 232 206 180 180 = true) : bonus 232 p ≤ 1 + Generated.soko1_2Potential.boulder 180 - Generated.soko1_2Potential.boulder 206 + bonus 206 (change p 206 (some 180)) := by
  have certified := compare3 p (guard563 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 206 (some 180))
  have normalized := agree75 _ _ (change_representative support p 206 (some 180) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check563 (p : Pattern) : (!pushGuard support p 232 206 180 180 || decide (bonus 232 p ≤ 1 + Generated.soko1_2Potential.boulder 180 - Generated.soko1_2Potential.boulder 206 + bonus 206 (change p 206 (some 180)))) = true :=
  check_of_implication _ _ (bound563 p)
theorem guard564 (p : Pattern) (guard : walkGuard soko1_2.board support p 232 258 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound564 (p : Pattern) (guard : walkGuard soko1_2.board support p 232 258 .south = true) : bonus 232 p ≤ bonus 258 p := by
  have certified := compare0 p (guard564 p guard)
  simpa only [at232, at258, Int.zero_add] using certified
theorem check564 (p : Pattern) : (!walkGuard soko1_2.board support p 232 258 .south || decide (bonus 232 p ≤ bonus 258 p)) = true :=
  check_of_implication _ _ (bound564 p)
theorem guard565 (p : Pattern) (guard : pushGuard support p 232 258 284 284 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound565 (p : Pattern) (guard : pushGuard support p 232 258 284 284 = true) : bonus 232 p ≤ 1 + Generated.soko1_2Potential.boulder 284 - Generated.soko1_2Potential.boulder 258 + bonus 258 (change p 258 (some 284)) := by
  have certified := compare3 p (guard565 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 258 (some 284))
  have normalized := agree75 _ _ (change_representative support p 258 (some 284) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check565 (p : Pattern) : (!pushGuard support p 232 258 284 284 || decide (bonus 232 p ≤ 1 + Generated.soko1_2Potential.boulder 284 - Generated.soko1_2Potential.boulder 258 + bonus 258 (change p 258 (some 284)))) = true :=
  check_of_implication _ _ (bound565 p)
theorem guard566 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 210 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound566 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 210 .north = true) : bonus 236 p ≤ bonus 210 p := by
  have certified := compare897 p (guard566 p guard)
  simpa only [at236, at210, Int.zero_add] using certified
theorem check566 (p : Pattern) : (!walkGuard soko1_2.board support p 236 210 .north || decide (bonus 236 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound566 p)
theorem guard567 (p : Pattern) (guard : pushGuard support p 236 210 184 184 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound567 (p : Pattern) (guard : pushGuard support p 236 210 184 184 = true) : bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder 184 - Generated.soko1_2Potential.boulder 210 + bonus 210 (change p 210 (some 184)) := by
  have certified := compare897 p (guard567 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 210 (some 184))
  have normalized := agree258 _ _ (change_representative support p 210 (some 184) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check567 (p : Pattern) : (!pushGuard support p 236 210 184 184 || decide (bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder 184 - Generated.soko1_2Potential.boulder 210 + bonus 210 (change p 210 (some 184)))) = true :=
  check_of_implication _ _ (bound567 p)
theorem guard568 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 262 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound568 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 262 .south = true) : bonus 236 p ≤ bonus 262 p := by
  have certified := compare897 p (guard568 p guard)
  simpa only [at236, at262, Int.zero_add] using certified
theorem check568 (p : Pattern) : (!walkGuard soko1_2.board support p 236 262 .south || decide (bonus 236 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound568 p)
theorem guard569 (p : Pattern) (guard : pushGuard support p 236 262 288 288 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound569 (p : Pattern) (guard : pushGuard support p 236 262 288 288 = true) : bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder 288 - Generated.soko1_2Potential.boulder 262 + bonus 262 (change p 262 (some 288)) := by
  have certified := compare5791 p (guard569 p guard)
  change d258 p ≤ (7 : Int) + d258 (change p 262 (some 288))
  have normalized := agree258 _ _ (change_representative support p 262 (some 288) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (7 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check569 (p : Pattern) : (!pushGuard support p 236 262 288 288 || decide (bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder 288 - Generated.soko1_2Potential.boulder 262 + bonus 262 (change p 262 (some 288)))) = true :=
  check_of_implication _ _ (bound569 p)
theorem guard570 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 237 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound570 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 237 .east = true) : bonus 236 p ≤ bonus 237 p := by
  have certified := compare897 p (guard570 p guard)
  simpa only [at236, at237, Int.zero_add] using certified
theorem check570 (p : Pattern) : (!walkGuard soko1_2.board support p 236 237 .east || decide (bonus 236 p ≤ bonus 237 p)) = true :=
  check_of_implication _ _ (bound570 p)
theorem guard571 (p : Pattern) (guard : pushGuard support p 236 237 238 238 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound571 (p : Pattern) (guard : pushGuard support p 236 237 238 238 = true) : bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some 238)) := by
  have certified := compare897 p (guard571 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 237 (some 238))
  have normalized := agree258 _ _ (change_representative support p 237 (some 238) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check571 (p : Pattern) : (!pushGuard support p 236 237 238 238 || decide (bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some 238)))) = true :=
  check_of_implication _ _ (bound571 p)
theorem guard572 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 211 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound572 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 211 .northEast = true) : bonus 236 p ≤ bonus 211 p := by
  have certified := compare897 p (guard572 p guard)
  simpa only [at236, at211, Int.zero_add] using certified
theorem check572 (p : Pattern) : (!walkGuard soko1_2.board support p 236 211 .northEast || decide (bonus 236 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound572 p)
theorem guard573 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 263 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound573 (p : Pattern) (guard : walkGuard soko1_2.board support p 236 263 .southEast = true) : bonus 236 p ≤ bonus 263 p := by
  have certified := compare897 p (guard573 p guard)
  simpa only [at236, at263, Int.zero_add] using certified
theorem check573 (p : Pattern) : (!walkGuard soko1_2.board support p 236 263 .southEast || decide (bonus 236 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound573 p)
theorem guard574 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 211 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound574 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 211 .north = true) : bonus 237 p ≤ bonus 211 p := by
  have certified := compare897 p (guard574 p guard)
  simpa only [at237, at211, Int.zero_add] using certified
theorem check574 (p : Pattern) : (!walkGuard soko1_2.board support p 237 211 .north || decide (bonus 237 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound574 p)
theorem guard575 (p : Pattern) (guard : pushGuard support p 237 211 185 185 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound575 (p : Pattern) (guard : pushGuard support p 237 211 185 185 = true) : bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some 185)) := by
  have certified := compare897 p (guard575 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 211 (some 185))
  have normalized := agree258 _ _ (change_representative support p 211 (some 185) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check575 (p : Pattern) : (!pushGuard support p 237 211 185 185 || decide (bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some 185)))) = true :=
  check_of_implication _ _ (bound575 p)
end NetHack.Sokoban12CostPartition
