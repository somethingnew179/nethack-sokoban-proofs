import NetHack.Sokoban12CostPartition.ActionBounds045
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1104 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 386 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1104 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 386 .east = true) : bonus 385 p ≤ bonus 386 p := by
  have certified := compare898 p (guard1104 p guard)
  simpa only [at385, at386, Int.zero_add] using certified
theorem check1104 (p : Pattern) : (!walkGuard soko1_2.board support p 385 386 .east || decide (bonus 385 p ≤ bonus 386 p)) = true :=
  check_of_implication _ _ (bound1104 p)
theorem guard1105 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 384 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1105 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 384 .west = true) : bonus 385 p ≤ bonus 384 p := by
  have certified := compare898 p (guard1105 p guard)
  simpa only [at385, at384, Int.zero_add] using certified
theorem check1105 (p : Pattern) : (!walkGuard soko1_2.board support p 385 384 .west || decide (bonus 385 p ≤ bonus 384 p)) = true :=
  check_of_implication _ _ (bound1105 p)
theorem guard1106 (p : Pattern) (guard : pushGuard support p 385 384 383 383 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1106 (p : Pattern) (guard : pushGuard support p 385 384 383 383 = true) : bonus 385 p ≤ 1 + Generated.soko1_2Potential.boulder 383 - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some 383)) := by
  have certified := compare1005 p (guard1106 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 384 (some 383))
  have normalized := agree0 _ _ (change_representative support p 384 (some 383) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1106 (p : Pattern) : (!pushGuard support p 385 384 383 383 || decide (bonus 385 p ≤ 1 + Generated.soko1_2Potential.boulder 383 - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some 383)))) = true :=
  check_of_implication _ _ (bound1106 p)
theorem guard1107 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 360 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1107 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 360 .northEast = true) : bonus 385 p ≤ bonus 360 p := by
  have certified := compare898 p (guard1107 p guard)
  simpa only [at385, at360, Int.zero_add] using certified
theorem check1107 (p : Pattern) : (!walkGuard soko1_2.board support p 385 360 .northEast || decide (bonus 385 p ≤ bonus 360 p)) = true :=
  check_of_implication _ _ (bound1107 p)
theorem guard1108 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 358 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1108 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 358 .northWest = true) : bonus 385 p ≤ bonus 358 p := by
  have certified := compare898 p (guard1108 p guard)
  simpa only [at385, at358, Int.zero_add] using certified
theorem check1108 (p : Pattern) : (!walkGuard soko1_2.board support p 385 358 .northWest || decide (bonus 385 p ≤ bonus 358 p)) = true :=
  check_of_implication _ _ (bound1108 p)
theorem guard1109 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 412 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1109 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 412 .southEast = true) : bonus 385 p ≤ bonus 412 p := by
  have certified := compare898 p (guard1109 p guard)
  simpa only [at385, at412, Int.zero_add] using certified
theorem check1109 (p : Pattern) : (!walkGuard soko1_2.board support p 385 412 .southEast || decide (bonus 385 p ≤ bonus 412 p)) = true :=
  check_of_implication _ _ (bound1109 p)
theorem guard1110 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 410 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1110 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 410 .southWest = true) : bonus 385 p ≤ bonus 410 p := by
  have certified := compare898 p (guard1110 p guard)
  simpa only [at385, at410, Int.zero_add] using certified
theorem check1110 (p : Pattern) : (!walkGuard soko1_2.board support p 385 410 .southWest || decide (bonus 385 p ≤ bonus 410 p)) = true :=
  check_of_implication _ _ (bound1110 p)
theorem guard1111 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 360 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1111 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 360 .north = true) : bonus 386 p ≤ bonus 360 p := by
  have certified := compare898 p (guard1111 p guard)
  simpa only [at386, at360, Int.zero_add] using certified
theorem check1111 (p : Pattern) : (!walkGuard soko1_2.board support p 386 360 .north || decide (bonus 386 p ≤ bonus 360 p)) = true :=
  check_of_implication _ _ (bound1111 p)
theorem guard1112 (p : Pattern) (guard : pushGuard support p 386 360 334 334 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1112 (p : Pattern) (guard : pushGuard support p 386 360 334 334 = true) : bonus 386 p ≤ 1 + Generated.soko1_2Potential.boulder 334 - Generated.soko1_2Potential.boulder 360 + bonus 360 (change p 360 (some 334)) := by
  have certified := compare1005 p (guard1112 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 360 (some 334))
  have normalized := agree0 _ _ (change_representative support p 360 (some 334) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1112 (p : Pattern) : (!pushGuard support p 386 360 334 334 || decide (bonus 386 p ≤ 1 + Generated.soko1_2Potential.boulder 334 - Generated.soko1_2Potential.boulder 360 + bonus 360 (change p 360 (some 334)))) = true :=
  check_of_implication _ _ (bound1112 p)
theorem guard1113 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 412 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1113 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 412 .south = true) : bonus 386 p ≤ bonus 412 p := by
  have certified := compare898 p (guard1113 p guard)
  simpa only [at386, at412, Int.zero_add] using certified
theorem check1113 (p : Pattern) : (!walkGuard soko1_2.board support p 386 412 .south || decide (bonus 386 p ≤ bonus 412 p)) = true :=
  check_of_implication _ _ (bound1113 p)
theorem guard1114 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 385 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1114 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 385 .west = true) : bonus 386 p ≤ bonus 385 p := by
  have certified := compare898 p (guard1114 p guard)
  simpa only [at386, at385, Int.zero_add] using certified
theorem check1114 (p : Pattern) : (!walkGuard soko1_2.board support p 386 385 .west || decide (bonus 386 p ≤ bonus 385 p)) = true :=
  check_of_implication _ _ (bound1114 p)
theorem guard1115 (p : Pattern) (guard : pushGuard support p 386 385 384 384 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1115 (p : Pattern) (guard : pushGuard support p 386 385 384 384 = true) : bonus 386 p ≤ 1 + Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some 384)) := by
  have certified := compare1005 p (guard1115 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 385 (some 384))
  have normalized := agree0 _ _ (change_representative support p 385 (some 384) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1115 (p : Pattern) : (!pushGuard support p 386 385 384 384 || decide (bonus 386 p ≤ 1 + Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some 384)))) = true :=
  check_of_implication _ _ (bound1115 p)
theorem guard1116 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 359 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1116 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 359 .northWest = true) : bonus 386 p ≤ bonus 359 p := by
  have certified := compare898 p (guard1116 p guard)
  simpa only [at386, at359, Int.zero_add] using certified
theorem check1116 (p : Pattern) : (!walkGuard soko1_2.board support p 386 359 .northWest || decide (bonus 386 p ≤ bonus 359 p)) = true :=
  check_of_implication _ _ (bound1116 p)
theorem guard1117 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 411 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1117 (p : Pattern) (guard : walkGuard soko1_2.board support p 386 411 .southWest = true) : bonus 386 p ≤ bonus 411 p := by
  have certified := compare898 p (guard1117 p guard)
  simpa only [at386, at411, Int.zero_add] using certified
theorem check1117 (p : Pattern) : (!walkGuard soko1_2.board support p 386 411 .southWest || decide (bonus 386 p ≤ bonus 411 p)) = true :=
  check_of_implication _ _ (bound1117 p)
theorem guard1118 (p : Pattern) (guard : walkGuard soko1_2.board support p 396 370 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1118 (p : Pattern) (guard : walkGuard soko1_2.board support p 396 370 .north = true) : bonus 396 p ≤ bonus 370 p := by
  have certified := compare897 p (guard1118 p guard)
  simpa only [at396, at370, Int.zero_add] using certified
theorem check1118 (p : Pattern) : (!walkGuard soko1_2.board support p 396 370 .north || decide (bonus 396 p ≤ bonus 370 p)) = true :=
  check_of_implication _ _ (bound1118 p)
theorem guard1119 (p : Pattern) (guard : walkGuard soko1_2.board support p 396 397 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1119 (p : Pattern) (guard : walkGuard soko1_2.board support p 396 397 .east = true) : bonus 396 p ≤ bonus 397 p := by
  have certified := compare897 p (guard1119 p guard)
  simpa only [at396, at397, Int.zero_add] using certified
theorem check1119 (p : Pattern) : (!walkGuard soko1_2.board support p 396 397 .east || decide (bonus 396 p ≤ bonus 397 p)) = true :=
  check_of_implication _ _ (bound1119 p)
theorem guard1120 (p : Pattern) (guard : walkGuard soko1_2.board support p 396 371 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1120 (p : Pattern) (guard : walkGuard soko1_2.board support p 396 371 .northEast = true) : bonus 396 p ≤ bonus 371 p := by
  have certified := compare897 p (guard1120 p guard)
  simpa only [at396, at371, Int.zero_add] using certified
theorem check1120 (p : Pattern) : (!walkGuard soko1_2.board support p 396 371 .northEast || decide (bonus 396 p ≤ bonus 371 p)) = true :=
  check_of_implication _ _ (bound1120 p)
theorem guard1121 (p : Pattern) (guard : walkGuard soko1_2.board support p 397 371 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1121 (p : Pattern) (guard : walkGuard soko1_2.board support p 397 371 .north = true) : bonus 397 p ≤ bonus 371 p := by
  have certified := compare897 p (guard1121 p guard)
  simpa only [at397, at371, Int.zero_add] using certified
theorem check1121 (p : Pattern) : (!walkGuard soko1_2.board support p 397 371 .north || decide (bonus 397 p ≤ bonus 371 p)) = true :=
  check_of_implication _ _ (bound1121 p)
theorem guard1122 (p : Pattern) (guard : pushGuard support p 397 371 345 345 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1122 (p : Pattern) (guard : pushGuard support p 397 371 345 345 = true) : bonus 397 p ≤ 1 + Generated.soko1_2Potential.boulder 345 - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some 345)) := by
  have certified := compare897 p (guard1122 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 371 (some 345))
  have normalized := agree258 _ _ (change_representative support p 371 (some 345) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1122 (p : Pattern) : (!pushGuard support p 397 371 345 345 || decide (bonus 397 p ≤ 1 + Generated.soko1_2Potential.boulder 345 - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some 345)))) = true :=
  check_of_implication _ _ (bound1122 p)
theorem guard1123 (p : Pattern) (guard : walkGuard soko1_2.board support p 397 396 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1123 (p : Pattern) (guard : walkGuard soko1_2.board support p 397 396 .west = true) : bonus 397 p ≤ bonus 396 p := by
  have certified := compare897 p (guard1123 p guard)
  simpa only [at397, at396, Int.zero_add] using certified
theorem check1123 (p : Pattern) : (!walkGuard soko1_2.board support p 397 396 .west || decide (bonus 397 p ≤ bonus 396 p)) = true :=
  check_of_implication _ _ (bound1123 p)
theorem guard1124 (p : Pattern) (guard : walkGuard soko1_2.board support p 397 372 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1124 (p : Pattern) (guard : walkGuard soko1_2.board support p 397 372 .northEast = true) : bonus 397 p ≤ bonus 372 p := by
  have certified := compare897 p (guard1124 p guard)
  simpa only [at397, at372, Int.zero_add] using certified
theorem check1124 (p : Pattern) : (!walkGuard soko1_2.board support p 397 372 .northEast || decide (bonus 397 p ≤ bonus 372 p)) = true :=
  check_of_implication _ _ (bound1124 p)
theorem guard1125 (p : Pattern) (guard : walkGuard soko1_2.board support p 397 370 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1125 (p : Pattern) (guard : walkGuard soko1_2.board support p 397 370 .northWest = true) : bonus 397 p ≤ bonus 370 p := by
  have certified := compare897 p (guard1125 p guard)
  simpa only [at397, at370, Int.zero_add] using certified
theorem check1125 (p : Pattern) : (!walkGuard soko1_2.board support p 397 370 .northWest || decide (bonus 397 p ≤ bonus 370 p)) = true :=
  check_of_implication _ _ (bound1125 p)
theorem guard1126 (p : Pattern) (guard : walkGuard soko1_2.board support p 399 373 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1126 (p : Pattern) (guard : walkGuard soko1_2.board support p 399 373 .north = true) : bonus 399 p ≤ bonus 373 p := by
  have certified := compare897 p (guard1126 p guard)
  simpa only [at399, at373, Int.zero_add] using certified
theorem check1126 (p : Pattern) : (!walkGuard soko1_2.board support p 399 373 .north || decide (bonus 399 p ≤ bonus 373 p)) = true :=
  check_of_implication _ _ (bound1126 p)
theorem guard1127 (p : Pattern) (guard : walkGuard soko1_2.board support p 399 400 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1127 (p : Pattern) (guard : walkGuard soko1_2.board support p 399 400 .east = true) : bonus 399 p ≤ bonus 400 p := by
  have certified := compare897 p (guard1127 p guard)
  simpa only [at399, at400, Int.zero_add] using certified
theorem check1127 (p : Pattern) : (!walkGuard soko1_2.board support p 399 400 .east || decide (bonus 399 p ≤ bonus 400 p)) = true :=
  check_of_implication _ _ (bound1127 p)
end NetHack.Sokoban12CostPartition
