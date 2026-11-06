import NetHack.Sokoban12CostPartition.ActionBounds043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1056 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 371 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1056 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 371 .west = true) : bonus 372 p ≤ bonus 371 p := by
  have certified := compare897 p (guard1056 p guard)
  simpa only [at372, at371, Int.zero_add] using certified
theorem check1056 (p : Pattern) : (!walkGuard soko1_2.board support p 372 371 .west || decide (bonus 372 p ≤ bonus 371 p)) = true :=
  check_of_implication _ _ (bound1056 p)
theorem guard1057 (p : Pattern) (guard : pushGuard support p 372 371 370 370 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1057 (p : Pattern) (guard : pushGuard support p 372 371 370 370 = true) : bonus 372 p ≤ 1 + Generated.soko1_2Potential.boulder 370 - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some 370)) := by
  have certified := compare2570 p (guard1057 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 371 (some 370))
  have normalized := agree258 _ _ (change_representative support p 371 (some 370) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1057 (p : Pattern) : (!pushGuard support p 372 371 370 370 || decide (bonus 372 p ≤ 1 + Generated.soko1_2Potential.boulder 370 - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some 370)))) = true :=
  check_of_implication _ _ (bound1057 p)
theorem guard1058 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 345 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1058 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 345 .northWest = true) : bonus 372 p ≤ bonus 345 p := by
  have certified := compare897 p (guard1058 p guard)
  simpa only [at372, at345, Int.zero_add] using certified
theorem check1058 (p : Pattern) : (!walkGuard soko1_2.board support p 372 345 .northWest || decide (bonus 372 p ≤ bonus 345 p)) = true :=
  check_of_implication _ _ (bound1058 p)
theorem guard1059 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 399 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1059 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 399 .southEast = true) : bonus 372 p ≤ bonus 399 p := by
  have certified := compare897 p (guard1059 p guard)
  simpa only [at372, at399, Int.zero_add] using certified
theorem check1059 (p : Pattern) : (!walkGuard soko1_2.board support p 372 399 .southEast || decide (bonus 372 p ≤ bonus 399 p)) = true :=
  check_of_implication _ _ (bound1059 p)
theorem guard1060 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 397 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1060 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 397 .southWest = true) : bonus 372 p ≤ bonus 397 p := by
  have certified := compare897 p (guard1060 p guard)
  simpa only [at372, at397, Int.zero_add] using certified
theorem check1060 (p : Pattern) : (!walkGuard soko1_2.board support p 372 397 .southWest || decide (bonus 372 p ≤ bonus 397 p)) = true :=
  check_of_implication _ _ (bound1060 p)
theorem guard1061 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 399 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1061 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 399 .south = true) : bonus 373 p ≤ bonus 399 p := by
  have certified := compare897 p (guard1061 p guard)
  simpa only [at373, at399, Int.zero_add] using certified
theorem check1061 (p : Pattern) : (!walkGuard soko1_2.board support p 373 399 .south || decide (bonus 373 p ≤ bonus 399 p)) = true :=
  check_of_implication _ _ (bound1061 p)
theorem guard1062 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 374 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1062 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 374 .east = true) : bonus 373 p ≤ bonus 374 p := by
  have certified := compare897 p (guard1062 p guard)
  simpa only [at373, at374, Int.zero_add] using certified
theorem check1062 (p : Pattern) : (!walkGuard soko1_2.board support p 373 374 .east || decide (bonus 373 p ≤ bonus 374 p)) = true :=
  check_of_implication _ _ (bound1062 p)
theorem guard1063 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 372 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1063 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 372 .west = true) : bonus 373 p ≤ bonus 372 p := by
  have certified := compare897 p (guard1063 p guard)
  simpa only [at373, at372, Int.zero_add] using certified
theorem check1063 (p : Pattern) : (!walkGuard soko1_2.board support p 373 372 .west || decide (bonus 373 p ≤ bonus 372 p)) = true :=
  check_of_implication _ _ (bound1063 p)
theorem guard1064 (p : Pattern) (guard : pushGuard support p 373 372 371 371 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1064 (p : Pattern) (guard : pushGuard support p 373 372 371 371 = true) : bonus 373 p ≤ 1 + Generated.soko1_2Potential.boulder 371 - Generated.soko1_2Potential.boulder 372 + bonus 372 (change p 372 (some 371)) := by
  have certified := compare897 p (guard1064 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 372 (some 371))
  have normalized := agree258 _ _ (change_representative support p 372 (some 371) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1064 (p : Pattern) : (!pushGuard support p 373 372 371 371 || decide (bonus 373 p ≤ 1 + Generated.soko1_2Potential.boulder 371 - Generated.soko1_2Potential.boulder 372 + bonus 372 (change p 372 (some 371)))) = true :=
  check_of_implication _ _ (bound1064 p)
theorem guard1065 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 348 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1065 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 348 .northEast = true) : bonus 373 p ≤ bonus 348 p := by
  have certified := compare897 p (guard1065 p guard)
  simpa only [at373, at348, Int.zero_add] using certified
theorem check1065 (p : Pattern) : (!walkGuard soko1_2.board support p 373 348 .northEast || decide (bonus 373 p ≤ bonus 348 p)) = true :=
  check_of_implication _ _ (bound1065 p)
theorem guard1066 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 400 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1066 (p : Pattern) (guard : walkGuard soko1_2.board support p 373 400 .southEast = true) : bonus 373 p ≤ bonus 400 p := by
  have certified := compare897 p (guard1066 p guard)
  simpa only [at373, at400, Int.zero_add] using certified
theorem check1066 (p : Pattern) : (!walkGuard soko1_2.board support p 373 400 .southEast || decide (bonus 373 p ≤ bonus 400 p)) = true :=
  check_of_implication _ _ (bound1066 p)
theorem guard1067 (p : Pattern) (guard : walkGuard soko1_2.board support p 374 348 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1067 (p : Pattern) (guard : walkGuard soko1_2.board support p 374 348 .north = true) : bonus 374 p ≤ bonus 348 p := by
  have certified := compare897 p (guard1067 p guard)
  simpa only [at374, at348, Int.zero_add] using certified
theorem check1067 (p : Pattern) : (!walkGuard soko1_2.board support p 374 348 .north || decide (bonus 374 p ≤ bonus 348 p)) = true :=
  check_of_implication _ _ (bound1067 p)
theorem guard1068 (p : Pattern) (guard : pushGuard support p 374 348 322 322 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1068 (p : Pattern) (guard : pushGuard support p 374 348 322 322 = true) : bonus 374 p ≤ 1 + Generated.soko1_2Potential.boulder 322 - Generated.soko1_2Potential.boulder 348 + bonus 348 (change p 348 (some 322)) := by
  have certified := compare5431 p (guard1068 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 348 (some 322))
  have normalized := agree258 _ _ (change_representative support p 348 (some 322) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1068 (p : Pattern) : (!pushGuard support p 374 348 322 322 || decide (bonus 374 p ≤ 1 + Generated.soko1_2Potential.boulder 322 - Generated.soko1_2Potential.boulder 348 + bonus 348 (change p 348 (some 322)))) = true :=
  check_of_implication _ _ (bound1068 p)
theorem guard1069 (p : Pattern) (guard : walkGuard soko1_2.board support p 374 400 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1069 (p : Pattern) (guard : walkGuard soko1_2.board support p 374 400 .south = true) : bonus 374 p ≤ bonus 400 p := by
  have certified := compare897 p (guard1069 p guard)
  simpa only [at374, at400, Int.zero_add] using certified
theorem check1069 (p : Pattern) : (!walkGuard soko1_2.board support p 374 400 .south || decide (bonus 374 p ≤ bonus 400 p)) = true :=
  check_of_implication _ _ (bound1069 p)
theorem guard1070 (p : Pattern) (guard : walkGuard soko1_2.board support p 374 373 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1070 (p : Pattern) (guard : walkGuard soko1_2.board support p 374 373 .west = true) : bonus 374 p ≤ bonus 373 p := by
  have certified := compare897 p (guard1070 p guard)
  simpa only [at374, at373, Int.zero_add] using certified
theorem check1070 (p : Pattern) : (!walkGuard soko1_2.board support p 374 373 .west || decide (bonus 374 p ≤ bonus 373 p)) = true :=
  check_of_implication _ _ (bound1070 p)
theorem guard1071 (p : Pattern) (guard : pushGuard support p 374 373 372 372 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1071 (p : Pattern) (guard : pushGuard support p 374 373 372 372 = true) : bonus 374 p ≤ 1 + Generated.soko1_2Potential.boulder 372 - Generated.soko1_2Potential.boulder 373 + bonus 373 (change p 373 (some 372)) := by
  have certified := compare5431 p (guard1071 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 373 (some 372))
  have normalized := agree258 _ _ (change_representative support p 373 (some 372) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1071 (p : Pattern) : (!pushGuard support p 374 373 372 372 || decide (bonus 374 p ≤ 1 + Generated.soko1_2Potential.boulder 372 - Generated.soko1_2Potential.boulder 373 + bonus 373 (change p 373 (some 372)))) = true :=
  check_of_implication _ _ (bound1071 p)
theorem guard1072 (p : Pattern) (guard : walkGuard soko1_2.board support p 374 399 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1072 (p : Pattern) (guard : walkGuard soko1_2.board support p 374 399 .southWest = true) : bonus 374 p ≤ bonus 399 p := by
  have certified := compare897 p (guard1072 p guard)
  simpa only [at374, at399, Int.zero_add] using certified
theorem check1072 (p : Pattern) : (!walkGuard soko1_2.board support p 374 399 .southWest || decide (bonus 374 p ≤ bonus 399 p)) = true :=
  check_of_implication _ _ (bound1072 p)
theorem guard1073 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 356 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1073 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 356 .north = true) : bonus 382 p ≤ bonus 356 p := by
  have certified := compare898 p (guard1073 p guard)
  simpa only [at382, at356, Int.zero_add] using certified
theorem check1073 (p : Pattern) : (!walkGuard soko1_2.board support p 382 356 .north || decide (bonus 382 p ≤ bonus 356 p)) = true :=
  check_of_implication _ _ (bound1073 p)
theorem guard1074 (p : Pattern) (guard : pushGuard support p 382 356 330 330 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1074 (p : Pattern) (guard : pushGuard support p 382 356 330 330 = true) : bonus 382 p ≤ 1 + Generated.soko1_2Potential.boulder 330 - Generated.soko1_2Potential.boulder 356 + bonus 356 (change p 356 (some 330)) := by
  have certified := compare1005 p (guard1074 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 356 (some 330))
  have normalized := agree0 _ _ (change_representative support p 356 (some 330) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1074 (p : Pattern) : (!pushGuard support p 382 356 330 330 || decide (bonus 382 p ≤ 1 + Generated.soko1_2Potential.boulder 330 - Generated.soko1_2Potential.boulder 356 + bonus 356 (change p 356 (some 330)))) = true :=
  check_of_implication _ _ (bound1074 p)
theorem guard1075 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 408 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1075 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 408 .south = true) : bonus 382 p ≤ bonus 408 p := by
  have certified := compare898 p (guard1075 p guard)
  simpa only [at382, at408, Int.zero_add] using certified
theorem check1075 (p : Pattern) : (!walkGuard soko1_2.board support p 382 408 .south || decide (bonus 382 p ≤ bonus 408 p)) = true :=
  check_of_implication _ _ (bound1075 p)
theorem guard1076 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 383 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1076 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 383 .east = true) : bonus 382 p ≤ bonus 383 p := by
  have certified := compare898 p (guard1076 p guard)
  simpa only [at382, at383, Int.zero_add] using certified
theorem check1076 (p : Pattern) : (!walkGuard soko1_2.board support p 382 383 .east || decide (bonus 382 p ≤ bonus 383 p)) = true :=
  check_of_implication _ _ (bound1076 p)
theorem guard1077 (p : Pattern) (guard : pushGuard support p 382 383 384 384 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1077 (p : Pattern) (guard : pushGuard support p 382 383 384 384 = true) : bonus 382 p ≤ 1 + Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some 384)) := by
  have certified := compare1005 p (guard1077 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 383 (some 384))
  have normalized := agree0 _ _ (change_representative support p 383 (some 384) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1077 (p : Pattern) : (!pushGuard support p 382 383 384 384 || decide (bonus 382 p ≤ 1 + Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some 384)))) = true :=
  check_of_implication _ _ (bound1077 p)
theorem guard1078 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 357 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1078 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 357 .northEast = true) : bonus 382 p ≤ bonus 357 p := by
  have certified := compare898 p (guard1078 p guard)
  simpa only [at382, at357, Int.zero_add] using certified
theorem check1078 (p : Pattern) : (!walkGuard soko1_2.board support p 382 357 .northEast || decide (bonus 382 p ≤ bonus 357 p)) = true :=
  check_of_implication _ _ (bound1078 p)
theorem guard1079 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 409 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1079 (p : Pattern) (guard : walkGuard soko1_2.board support p 382 409 .southEast = true) : bonus 382 p ≤ bonus 409 p := by
  have certified := compare898 p (guard1079 p guard)
  simpa only [at382, at409, Int.zero_add] using certified
theorem check1079 (p : Pattern) : (!walkGuard soko1_2.board support p 382 409 .southEast || decide (bonus 382 p ≤ bonus 409 p)) = true :=
  check_of_implication _ _ (bound1079 p)
end NetHack.Sokoban12CostPartition
