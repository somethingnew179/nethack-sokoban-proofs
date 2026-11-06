import NetHack.Sokoban12CostPartition.ActionBounds046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1128 (p : Pattern) (guard : walkGuard soko1_2.board support p 399 374 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1128 (p : Pattern) (guard : walkGuard soko1_2.board support p 399 374 .northEast = true) : bonus 399 p ≤ bonus 374 p := by
  have certified := compare897 p (guard1128 p guard)
  simpa only [at399, at374, Int.zero_add] using certified
theorem check1128 (p : Pattern) : (!walkGuard soko1_2.board support p 399 374 .northEast || decide (bonus 399 p ≤ bonus 374 p)) = true :=
  check_of_implication _ _ (bound1128 p)
theorem guard1129 (p : Pattern) (guard : walkGuard soko1_2.board support p 399 372 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1129 (p : Pattern) (guard : walkGuard soko1_2.board support p 399 372 .northWest = true) : bonus 399 p ≤ bonus 372 p := by
  have certified := compare897 p (guard1129 p guard)
  simpa only [at399, at372, Int.zero_add] using certified
theorem check1129 (p : Pattern) : (!walkGuard soko1_2.board support p 399 372 .northWest || decide (bonus 399 p ≤ bonus 372 p)) = true :=
  check_of_implication _ _ (bound1129 p)
theorem guard1130 (p : Pattern) (guard : walkGuard soko1_2.board support p 400 374 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1130 (p : Pattern) (guard : walkGuard soko1_2.board support p 400 374 .north = true) : bonus 400 p ≤ bonus 374 p := by
  have certified := compare897 p (guard1130 p guard)
  simpa only [at400, at374, Int.zero_add] using certified
theorem check1130 (p : Pattern) : (!walkGuard soko1_2.board support p 400 374 .north || decide (bonus 400 p ≤ bonus 374 p)) = true :=
  check_of_implication _ _ (bound1130 p)
theorem guard1131 (p : Pattern) (guard : pushGuard support p 400 374 348 348 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1131 (p : Pattern) (guard : pushGuard support p 400 374 348 348 = true) : bonus 400 p ≤ 1 + Generated.soko1_2Potential.boulder 348 - Generated.soko1_2Potential.boulder 374 + bonus 374 (change p 374 (some 348)) := by
  have certified := compare5431 p (guard1131 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 374 (some 348))
  have normalized := agree258 _ _ (change_representative support p 374 (some 348) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1131 (p : Pattern) : (!pushGuard support p 400 374 348 348 || decide (bonus 400 p ≤ 1 + Generated.soko1_2Potential.boulder 348 - Generated.soko1_2Potential.boulder 374 + bonus 374 (change p 374 (some 348)))) = true :=
  check_of_implication _ _ (bound1131 p)
theorem guard1132 (p : Pattern) (guard : walkGuard soko1_2.board support p 400 399 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1132 (p : Pattern) (guard : walkGuard soko1_2.board support p 400 399 .west = true) : bonus 400 p ≤ bonus 399 p := by
  have certified := compare897 p (guard1132 p guard)
  simpa only [at400, at399, Int.zero_add] using certified
theorem check1132 (p : Pattern) : (!walkGuard soko1_2.board support p 400 399 .west || decide (bonus 400 p ≤ bonus 399 p)) = true :=
  check_of_implication _ _ (bound1132 p)
theorem guard1133 (p : Pattern) (guard : walkGuard soko1_2.board support p 400 373 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1133 (p : Pattern) (guard : walkGuard soko1_2.board support p 400 373 .northWest = true) : bonus 400 p ≤ bonus 373 p := by
  have certified := compare897 p (guard1133 p guard)
  simpa only [at400, at373, Int.zero_add] using certified
theorem check1133 (p : Pattern) : (!walkGuard soko1_2.board support p 400 373 .northWest || decide (bonus 400 p ≤ bonus 373 p)) = true :=
  check_of_implication _ _ (bound1133 p)
theorem guard1134 (p : Pattern) (guard : walkGuard soko1_2.board support p 408 382 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1134 (p : Pattern) (guard : walkGuard soko1_2.board support p 408 382 .north = true) : bonus 408 p ≤ bonus 382 p := by
  have certified := compare898 p (guard1134 p guard)
  simpa only [at408, at382, Int.zero_add] using certified
theorem check1134 (p : Pattern) : (!walkGuard soko1_2.board support p 408 382 .north || decide (bonus 408 p ≤ bonus 382 p)) = true :=
  check_of_implication _ _ (bound1134 p)
theorem guard1135 (p : Pattern) (guard : pushGuard support p 408 382 356 356 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1135 (p : Pattern) (guard : pushGuard support p 408 382 356 356 = true) : bonus 408 p ≤ 1 + Generated.soko1_2Potential.boulder 356 - Generated.soko1_2Potential.boulder 382 + bonus 382 (change p 382 (some 356)) := by
  have certified := compare1005 p (guard1135 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 382 (some 356))
  have normalized := agree0 _ _ (change_representative support p 382 (some 356) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1135 (p : Pattern) : (!pushGuard support p 408 382 356 356 || decide (bonus 408 p ≤ 1 + Generated.soko1_2Potential.boulder 356 - Generated.soko1_2Potential.boulder 382 + bonus 382 (change p 382 (some 356)))) = true :=
  check_of_implication _ _ (bound1135 p)
theorem guard1136 (p : Pattern) (guard : walkGuard soko1_2.board support p 408 409 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1136 (p : Pattern) (guard : walkGuard soko1_2.board support p 408 409 .east = true) : bonus 408 p ≤ bonus 409 p := by
  have certified := compare898 p (guard1136 p guard)
  simpa only [at408, at409, Int.zero_add] using certified
theorem check1136 (p : Pattern) : (!walkGuard soko1_2.board support p 408 409 .east || decide (bonus 408 p ≤ bonus 409 p)) = true :=
  check_of_implication _ _ (bound1136 p)
theorem guard1137 (p : Pattern) (guard : pushGuard support p 408 409 410 410 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1137 (p : Pattern) (guard : pushGuard support p 408 409 410 410 = true) : bonus 408 p ≤ 1 + Generated.soko1_2Potential.boulder 410 - Generated.soko1_2Potential.boulder 409 + bonus 409 (change p 409 (some 410)) := by
  have certified := compare1005 p (guard1137 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 409 (some 410))
  have normalized := agree0 _ _ (change_representative support p 409 (some 410) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1137 (p : Pattern) : (!pushGuard support p 408 409 410 410 || decide (bonus 408 p ≤ 1 + Generated.soko1_2Potential.boulder 410 - Generated.soko1_2Potential.boulder 409 + bonus 409 (change p 409 (some 410)))) = true :=
  check_of_implication _ _ (bound1137 p)
theorem guard1138 (p : Pattern) (guard : walkGuard soko1_2.board support p 408 383 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1138 (p : Pattern) (guard : walkGuard soko1_2.board support p 408 383 .northEast = true) : bonus 408 p ≤ bonus 383 p := by
  have certified := compare898 p (guard1138 p guard)
  simpa only [at408, at383, Int.zero_add] using certified
theorem check1138 (p : Pattern) : (!walkGuard soko1_2.board support p 408 383 .northEast || decide (bonus 408 p ≤ bonus 383 p)) = true :=
  check_of_implication _ _ (bound1138 p)
theorem guard1139 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 383 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1139 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 383 .north = true) : bonus 409 p ≤ bonus 383 p := by
  have certified := compare898 p (guard1139 p guard)
  simpa only [at409, at383, Int.zero_add] using certified
theorem check1139 (p : Pattern) : (!walkGuard soko1_2.board support p 409 383 .north || decide (bonus 409 p ≤ bonus 383 p)) = true :=
  check_of_implication _ _ (bound1139 p)
theorem guard1140 (p : Pattern) (guard : pushGuard support p 409 383 357 357 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1140 (p : Pattern) (guard : pushGuard support p 409 383 357 357 = true) : bonus 409 p ≤ 1 + Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some 357)) := by
  have certified := compare1005 p (guard1140 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 383 (some 357))
  have normalized := agree0 _ _ (change_representative support p 383 (some 357) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1140 (p : Pattern) : (!pushGuard support p 409 383 357 357 || decide (bonus 409 p ≤ 1 + Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some 357)))) = true :=
  check_of_implication _ _ (bound1140 p)
theorem guard1141 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 410 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1141 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 410 .east = true) : bonus 409 p ≤ bonus 410 p := by
  have certified := compare898 p (guard1141 p guard)
  simpa only [at409, at410, Int.zero_add] using certified
theorem check1141 (p : Pattern) : (!walkGuard soko1_2.board support p 409 410 .east || decide (bonus 409 p ≤ bonus 410 p)) = true :=
  check_of_implication _ _ (bound1141 p)
theorem guard1142 (p : Pattern) (guard : pushGuard support p 409 410 411 411 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1142 (p : Pattern) (guard : pushGuard support p 409 410 411 411 = true) : bonus 409 p ≤ 1 + Generated.soko1_2Potential.boulder 411 - Generated.soko1_2Potential.boulder 410 + bonus 410 (change p 410 (some 411)) := by
  have certified := compare1005 p (guard1142 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 410 (some 411))
  have normalized := agree0 _ _ (change_representative support p 410 (some 411) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1142 (p : Pattern) : (!pushGuard support p 409 410 411 411 || decide (bonus 409 p ≤ 1 + Generated.soko1_2Potential.boulder 411 - Generated.soko1_2Potential.boulder 410 + bonus 410 (change p 410 (some 411)))) = true :=
  check_of_implication _ _ (bound1142 p)
theorem guard1143 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 408 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1143 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 408 .west = true) : bonus 409 p ≤ bonus 408 p := by
  have certified := compare898 p (guard1143 p guard)
  simpa only [at409, at408, Int.zero_add] using certified
theorem check1143 (p : Pattern) : (!walkGuard soko1_2.board support p 409 408 .west || decide (bonus 409 p ≤ bonus 408 p)) = true :=
  check_of_implication _ _ (bound1143 p)
theorem guard1144 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 384 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1144 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 384 .northEast = true) : bonus 409 p ≤ bonus 384 p := by
  have certified := compare898 p (guard1144 p guard)
  simpa only [at409, at384, Int.zero_add] using certified
theorem check1144 (p : Pattern) : (!walkGuard soko1_2.board support p 409 384 .northEast || decide (bonus 409 p ≤ bonus 384 p)) = true :=
  check_of_implication _ _ (bound1144 p)
theorem guard1145 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 382 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1145 (p : Pattern) (guard : walkGuard soko1_2.board support p 409 382 .northWest = true) : bonus 409 p ≤ bonus 382 p := by
  have certified := compare898 p (guard1145 p guard)
  simpa only [at409, at382, Int.zero_add] using certified
theorem check1145 (p : Pattern) : (!walkGuard soko1_2.board support p 409 382 .northWest || decide (bonus 409 p ≤ bonus 382 p)) = true :=
  check_of_implication _ _ (bound1145 p)
theorem guard1146 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 384 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1146 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 384 .north = true) : bonus 410 p ≤ bonus 384 p := by
  have certified := compare898 p (guard1146 p guard)
  simpa only [at410, at384, Int.zero_add] using certified
theorem check1146 (p : Pattern) : (!walkGuard soko1_2.board support p 410 384 .north || decide (bonus 410 p ≤ bonus 384 p)) = true :=
  check_of_implication _ _ (bound1146 p)
theorem guard1147 (p : Pattern) (guard : pushGuard support p 410 384 358 358 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1147 (p : Pattern) (guard : pushGuard support p 410 384 358 358 = true) : bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some 358)) := by
  have certified := compare1005 p (guard1147 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 384 (some 358))
  have normalized := agree0 _ _ (change_representative support p 384 (some 358) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1147 (p : Pattern) : (!pushGuard support p 410 384 358 358 || decide (bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some 358)))) = true :=
  check_of_implication _ _ (bound1147 p)
theorem guard1148 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 411 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1148 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 411 .east = true) : bonus 410 p ≤ bonus 411 p := by
  have certified := compare898 p (guard1148 p guard)
  simpa only [at410, at411, Int.zero_add] using certified
theorem check1148 (p : Pattern) : (!walkGuard soko1_2.board support p 410 411 .east || decide (bonus 410 p ≤ bonus 411 p)) = true :=
  check_of_implication _ _ (bound1148 p)
theorem guard1149 (p : Pattern) (guard : pushGuard support p 410 411 412 412 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1149 (p : Pattern) (guard : pushGuard support p 410 411 412 412 = true) : bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder 412 - Generated.soko1_2Potential.boulder 411 + bonus 411 (change p 411 (some 412)) := by
  have certified := compare1005 p (guard1149 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 411 (some 412))
  have normalized := agree0 _ _ (change_representative support p 411 (some 412) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1149 (p : Pattern) : (!pushGuard support p 410 411 412 412 || decide (bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder 412 - Generated.soko1_2Potential.boulder 411 + bonus 411 (change p 411 (some 412)))) = true :=
  check_of_implication _ _ (bound1149 p)
theorem guard1150 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 409 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1150 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 409 .west = true) : bonus 410 p ≤ bonus 409 p := by
  have certified := compare898 p (guard1150 p guard)
  simpa only [at410, at409, Int.zero_add] using certified
theorem check1150 (p : Pattern) : (!walkGuard soko1_2.board support p 410 409 .west || decide (bonus 410 p ≤ bonus 409 p)) = true :=
  check_of_implication _ _ (bound1150 p)
theorem guard1151 (p : Pattern) (guard : pushGuard support p 410 409 408 408 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1151 (p : Pattern) (guard : pushGuard support p 410 409 408 408 = true) : bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder 408 - Generated.soko1_2Potential.boulder 409 + bonus 409 (change p 409 (some 408)) := by
  have certified := compare1005 p (guard1151 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 409 (some 408))
  have normalized := agree0 _ _ (change_representative support p 409 (some 408) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1151 (p : Pattern) : (!pushGuard support p 410 409 408 408 || decide (bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder 408 - Generated.soko1_2Potential.boulder 409 + bonus 409 (change p 409 (some 408)))) = true :=
  check_of_implication _ _ (bound1151 p)
end NetHack.Sokoban12CostPartition
