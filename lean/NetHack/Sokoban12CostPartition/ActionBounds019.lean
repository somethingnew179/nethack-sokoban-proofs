import NetHack.Sokoban12CostPartition.ActionBounds018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard456 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 218 .southWest = true) : d917 p = 1 := by
  change (!(p 193) && !false && !(true && false && (p 192))) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, h192, h193] at guard ⊢
theorem bound456 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 218 .southWest = true) : bonus 193 p ≤ bonus 218 p := by
  have certified := compare5047 p (guard456 p guard)
  simpa only [at193, at218, Int.zero_add] using certified
theorem check456 (p : Pattern) : (!walkGuard soko1_2.board support p 193 218 .southWest || decide (bonus 193 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound456 p)
theorem guard457 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 168 .north = true) : d770 p = 1 := by
  change (!false && !(p 168) && !false) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound457 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 168 .north = true) : bonus 194 p ≤ bonus 168 p := by
  have certified := compare2997 p (guard457 p guard)
  simpa only [at194, at168, Int.zero_add] using certified
theorem check457 (p : Pattern) : (!walkGuard soko1_2.board support p 194 168 .north || decide (bonus 194 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound457 p)
theorem guard458 (p : Pattern) (guard : pushGuard support p 194 168 142 142 = true) : d769 p = 1 := by
  change (!false && (!true || (p 168)) && !false && (!false || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d769, h168] at guard ⊢
theorem bound458 (p : Pattern) (guard : pushGuard support p 194 168 142 142 = true) : bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder 142 - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some 142)) := by
  have certified := compare3048 p (guard458 p guard)
  change d258 p ≤ (1 : Int) + d430 (change p 168 (some 142))
  have normalized := agree430 _ _ (change_representative support p 168 (some 142) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d430 (change p 168 none)
  rw [sub1091]
  exact certified
theorem check458 (p : Pattern) : (!pushGuard support p 194 168 142 142 || decide (bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder 142 - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some 142)))) = true :=
  check_of_implication _ _ (bound458 p)
theorem guard459 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 220 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound459 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 220 .south = true) : bonus 194 p ≤ bonus 220 p := by
  have certified := compare897 p (guard459 p guard)
  simpa only [at194, at220, Int.zero_add] using certified
theorem check459 (p : Pattern) : (!walkGuard soko1_2.board support p 194 220 .south || decide (bonus 194 p ≤ bonus 220 p)) = true :=
  check_of_implication _ _ (bound459 p)
theorem guard460 (p : Pattern) (guard : pushGuard support p 194 220 246 246 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound460 (p : Pattern) (guard : pushGuard support p 194 220 246 246 = true) : bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder 246 - Generated.soko1_2Potential.boulder 220 + bonus 220 (change p 220 (some 246)) := by
  have certified := compare5431 p (guard460 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 220 (some 246))
  have normalized := agree258 _ _ (change_representative support p 220 (some 246) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check460 (p : Pattern) : (!pushGuard support p 194 220 246 246 || decide (bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder 246 - Generated.soko1_2Potential.boulder 220 + bonus 220 (change p 220 (some 246)))) = true :=
  check_of_implication _ _ (bound460 p)
theorem guard461 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 193 .west = true) : d917 p = 1 := by
  change (!false && !(p 193) && !false) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound461 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 193 .west = true) : bonus 194 p ≤ bonus 193 p := by
  have certified := compare2879 p (guard461 p guard)
  simpa only [at194, at193, Int.zero_add] using certified
theorem check461 (p : Pattern) : (!walkGuard soko1_2.board support p 194 193 .west || decide (bonus 194 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound461 p)
theorem guard462 (p : Pattern) (guard : pushGuard support p 194 193 192 192 = true) : d1176 p = 1 := by
  change (!false && (!true || (p 193)) && !(p 192) && (!(p 192) || false)) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d916, d1176, h192, h193] at guard ⊢
theorem bound462 (p : Pattern) (guard : pushGuard support p 194 193 192 192 = true) : bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some 192)) := by
  have certified := compare5502 p (guard462 p guard)
  change d258 p ≤ (0 : Int) + d658 (change p 193 (some 192))
  have normalized := agree658 _ _ (change_representative support p 193 (some 192) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d658 (change p 193 (some 192))
  rw [sub2274]
  exact certified
theorem check462 (p : Pattern) : (!pushGuard support p 194 193 192 192 || decide (bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some 192)))) = true :=
  check_of_implication _ _ (bound462 p)
theorem guard463 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 169 .northEast = true) : d770 p = 1 := by
  change (!false && !false && !(true && (p 168) && true)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound463 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 169 .northEast = true) : bonus 194 p ≤ bonus 169 p := by
  have certified := compare5522 p (guard463 p guard)
  simpa only [at194, at169, Int.zero_add] using certified
theorem check463 (p : Pattern) : (!walkGuard soko1_2.board support p 194 169 .northEast || decide (bonus 194 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound463 p)
theorem guard464 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 167 .northWest = true) : d1133 p = 1 := by
  change (!false && !false && !(true && (p 168) && (p 193))) = true at guard
  cases h168 : p 168 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d1133, h168, h193] at guard ⊢
theorem bound464 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 167 .northWest = true) : bonus 194 p ≤ bonus 167 p := by
  have certified := compare3093 p (guard464 p guard)
  simpa only [at194, at167, Int.zero_add] using certified
theorem check464 (p : Pattern) : (!walkGuard soko1_2.board support p 194 167 .northWest || decide (bonus 194 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound464 p)
theorem guard465 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 219 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 193))) = true at guard
  cases h193 : p 193
  all_goals simp [d1, h193] at guard ⊢
theorem bound465 (p : Pattern) (guard : walkGuard soko1_2.board support p 194 219 .southWest = true) : bonus 194 p ≤ bonus 219 p := by
  have certified := compare897 p (guard465 p guard)
  simpa only [at194, at219, Int.zero_add] using certified
theorem check465 (p : Pattern) : (!walkGuard soko1_2.board support p 194 219 .southWest || decide (bonus 194 p ≤ bonus 219 p)) = true :=
  check_of_implication _ _ (bound465 p)
theorem guard466 (p : Pattern) (guard : walkGuard soko1_2.board support p 206 180 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound466 (p : Pattern) (guard : walkGuard soko1_2.board support p 206 180 .north = true) : bonus 206 p ≤ bonus 180 p := by
  have certified := compare0 p (guard466 p guard)
  simpa only [at206, at180, Int.zero_add] using certified
theorem check466 (p : Pattern) : (!walkGuard soko1_2.board support p 206 180 .north || decide (bonus 206 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound466 p)
theorem guard467 (p : Pattern) (guard : pushGuard support p 206 180 154 154 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound467 (p : Pattern) (guard : pushGuard support p 206 180 154 154 = true) : bonus 206 p ≤ 1 + Generated.soko1_2Potential.boulder 154 - Generated.soko1_2Potential.boulder 180 + bonus 180 (change p 180 (some 154)) := by
  have certified := compare3 p (guard467 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 180 (some 154))
  have normalized := agree75 _ _ (change_representative support p 180 (some 154) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check467 (p : Pattern) : (!pushGuard support p 206 180 154 154 || decide (bonus 206 p ≤ 1 + Generated.soko1_2Potential.boulder 154 - Generated.soko1_2Potential.boulder 180 + bonus 180 (change p 180 (some 154)))) = true :=
  check_of_implication _ _ (bound467 p)
theorem guard468 (p : Pattern) (guard : walkGuard soko1_2.board support p 206 232 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound468 (p : Pattern) (guard : walkGuard soko1_2.board support p 206 232 .south = true) : bonus 206 p ≤ bonus 232 p := by
  have certified := compare0 p (guard468 p guard)
  simpa only [at206, at232, Int.zero_add] using certified
theorem check468 (p : Pattern) : (!walkGuard soko1_2.board support p 206 232 .south || decide (bonus 206 p ≤ bonus 232 p)) = true :=
  check_of_implication _ _ (bound468 p)
theorem guard469 (p : Pattern) (guard : pushGuard support p 206 232 258 258 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound469 (p : Pattern) (guard : pushGuard support p 206 232 258 258 = true) : bonus 206 p ≤ 1 + Generated.soko1_2Potential.boulder 258 - Generated.soko1_2Potential.boulder 232 + bonus 232 (change p 232 (some 258)) := by
  have certified := compare3 p (guard469 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 232 (some 258))
  have normalized := agree75 _ _ (change_representative support p 232 (some 258) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check469 (p : Pattern) : (!pushGuard support p 206 232 258 258 || decide (bonus 206 p ≤ 1 + Generated.soko1_2Potential.boulder 258 - Generated.soko1_2Potential.boulder 232 + bonus 232 (change p 232 (some 258)))) = true :=
  check_of_implication _ _ (bound469 p)
theorem guard470 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 184 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound470 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 184 .north = true) : bonus 210 p ≤ bonus 184 p := by
  have certified := compare897 p (guard470 p guard)
  simpa only [at210, at184, Int.zero_add] using certified
theorem check470 (p : Pattern) : (!walkGuard soko1_2.board support p 210 184 .north || decide (bonus 210 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound470 p)
theorem guard471 (p : Pattern) (guard : pushGuard support p 210 184 158 158 = true) : d742 p = 1 := by
  change (!false && (!false || false) && !(p 158) && (!(p 158) || false)) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d742, h158] at guard ⊢
theorem bound471 (p : Pattern) (guard : pushGuard support p 210 184 158 158 = true) : bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.boulder 184 + bonus 184 (change p 184 (some 158)) := by
  have certified := compare5573 p (guard471 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 184 (some 158))
  have normalized := agree258 _ _ (change_representative support p 184 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 (some 158))
  rw [sub2348]
  exact certified
theorem check471 (p : Pattern) : (!pushGuard support p 210 184 158 158 || decide (bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.boulder 184 + bonus 184 (change p 184 (some 158)))) = true :=
  check_of_implication _ _ (bound471 p)
theorem guard472 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 236 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound472 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 236 .south = true) : bonus 210 p ≤ bonus 236 p := by
  have certified := compare897 p (guard472 p guard)
  simpa only [at210, at236, Int.zero_add] using certified
theorem check472 (p : Pattern) : (!walkGuard soko1_2.board support p 210 236 .south || decide (bonus 210 p ≤ bonus 236 p)) = true :=
  check_of_implication _ _ (bound472 p)
theorem guard473 (p : Pattern) (guard : pushGuard support p 210 236 262 262 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound473 (p : Pattern) (guard : pushGuard support p 210 236 262 262 = true) : bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder 262 - Generated.soko1_2Potential.boulder 236 + bonus 236 (change p 236 (some 262)) := by
  have certified := compare2570 p (guard473 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 236 (some 262))
  have normalized := agree258 _ _ (change_representative support p 236 (some 262) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check473 (p : Pattern) : (!pushGuard support p 210 236 262 262 || decide (bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder 262 - Generated.soko1_2Potential.boulder 236 + bonus 236 (change p 236 (some 262)))) = true :=
  check_of_implication _ _ (bound473 p)
theorem guard474 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 211 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound474 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 211 .east = true) : bonus 210 p ≤ bonus 211 p := by
  have certified := compare897 p (guard474 p guard)
  simpa only [at210, at211, Int.zero_add] using certified
theorem check474 (p : Pattern) : (!walkGuard soko1_2.board support p 210 211 .east || decide (bonus 210 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound474 p)
theorem guard475 (p : Pattern) (guard : pushGuard support p 210 211 212 212 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound475 (p : Pattern) (guard : pushGuard support p 210 211 212 212 = true) : bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some 212)) := by
  have certified := compare897 p (guard475 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 211 (some 212))
  have normalized := agree258 _ _ (change_representative support p 211 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check475 (p : Pattern) : (!pushGuard support p 210 211 212 212 || decide (bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some 212)))) = true :=
  check_of_implication _ _ (bound475 p)
theorem guard476 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 185 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound476 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 185 .northEast = true) : bonus 210 p ≤ bonus 185 p := by
  have certified := compare897 p (guard476 p guard)
  simpa only [at210, at185, Int.zero_add] using certified
theorem check476 (p : Pattern) : (!walkGuard soko1_2.board support p 210 185 .northEast || decide (bonus 210 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound476 p)
theorem guard477 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 237 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound477 (p : Pattern) (guard : walkGuard soko1_2.board support p 210 237 .southEast = true) : bonus 210 p ≤ bonus 237 p := by
  have certified := compare897 p (guard477 p guard)
  simpa only [at210, at237, Int.zero_add] using certified
theorem check477 (p : Pattern) : (!walkGuard soko1_2.board support p 210 237 .southEast || decide (bonus 210 p ≤ bonus 237 p)) = true :=
  check_of_implication _ _ (bound477 p)
theorem guard478 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 185 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound478 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 185 .north = true) : bonus 211 p ≤ bonus 185 p := by
  have certified := compare897 p (guard478 p guard)
  simpa only [at211, at185, Int.zero_add] using certified
theorem check478 (p : Pattern) : (!walkGuard soko1_2.board support p 211 185 .north || decide (bonus 211 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound478 p)
theorem guard479 (p : Pattern) (guard : pushGuard support p 211 185 159 159 = true) : d794 p = 1 := by
  change (!false && (!false || false) && !(p 159) && (!(p 159) || false)) = true at guard
  cases h159 : p 159
  all_goals simp [d0, d1, d794, h159] at guard ⊢
theorem bound479 (p : Pattern) (guard : pushGuard support p 211 185 159 159 = true) : bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some 159)) := by
  have certified := compare5619 p (guard479 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 185 (some 159))
  have normalized := agree258 _ _ (change_representative support p 185 (some 159) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 (some 159))
  rw [sub2424]
  exact certified
theorem check479 (p : Pattern) : (!pushGuard support p 211 185 159 159 || decide (bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some 159)))) = true :=
  check_of_implication _ _ (bound479 p)
end NetHack.Sokoban12CostPartition
