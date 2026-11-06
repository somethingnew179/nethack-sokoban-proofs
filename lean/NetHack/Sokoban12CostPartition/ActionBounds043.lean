import NetHack.Sokoban12CostPartition.ActionBounds042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1032 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 386 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1032 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 386 .southEast = true) : bonus 359 p ≤ bonus 386 p := by
  have certified := compare898 p (guard1032 p guard)
  simpa only [at359, at386, Int.zero_add] using certified
theorem check1032 (p : Pattern) : (!walkGuard soko1_2.board support p 359 386 .southEast || decide (bonus 359 p ≤ bonus 386 p)) = true :=
  check_of_implication _ _ (bound1032 p)
theorem guard1033 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 384 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1033 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 384 .southWest = true) : bonus 359 p ≤ bonus 384 p := by
  have certified := compare898 p (guard1033 p guard)
  simpa only [at359, at384, Int.zero_add] using certified
theorem check1033 (p : Pattern) : (!walkGuard soko1_2.board support p 359 384 .southWest || decide (bonus 359 p ≤ bonus 384 p)) = true :=
  check_of_implication _ _ (bound1033 p)
theorem guard1034 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 334 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1034 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 334 .north = true) : bonus 360 p ≤ bonus 334 p := by
  have certified := compare898 p (guard1034 p guard)
  simpa only [at360, at334, Int.zero_add] using certified
theorem check1034 (p : Pattern) : (!walkGuard soko1_2.board support p 360 334 .north || decide (bonus 360 p ≤ bonus 334 p)) = true :=
  check_of_implication _ _ (bound1034 p)
theorem guard1035 (p : Pattern) (guard : pushGuard support p 360 334 308 308 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1035 (p : Pattern) (guard : pushGuard support p 360 334 308 308 = true) : bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder 308 - Generated.soko1_2Potential.boulder 334 + bonus 334 (change p 334 (some 308)) := by
  have certified := compare1005 p (guard1035 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 334 (some 308))
  have normalized := agree0 _ _ (change_representative support p 334 (some 308) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1035 (p : Pattern) : (!pushGuard support p 360 334 308 308 || decide (bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder 308 - Generated.soko1_2Potential.boulder 334 + bonus 334 (change p 334 (some 308)))) = true :=
  check_of_implication _ _ (bound1035 p)
theorem guard1036 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 386 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1036 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 386 .south = true) : bonus 360 p ≤ bonus 386 p := by
  have certified := compare898 p (guard1036 p guard)
  simpa only [at360, at386, Int.zero_add] using certified
theorem check1036 (p : Pattern) : (!walkGuard soko1_2.board support p 360 386 .south || decide (bonus 360 p ≤ bonus 386 p)) = true :=
  check_of_implication _ _ (bound1036 p)
theorem guard1037 (p : Pattern) (guard : pushGuard support p 360 386 412 412 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1037 (p : Pattern) (guard : pushGuard support p 360 386 412 412 = true) : bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder 412 - Generated.soko1_2Potential.boulder 386 + bonus 386 (change p 386 (some 412)) := by
  have certified := compare1005 p (guard1037 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 386 (some 412))
  have normalized := agree0 _ _ (change_representative support p 386 (some 412) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1037 (p : Pattern) : (!pushGuard support p 360 386 412 412 || decide (bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder 412 - Generated.soko1_2Potential.boulder 386 + bonus 386 (change p 386 (some 412)))) = true :=
  check_of_implication _ _ (bound1037 p)
theorem guard1038 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 359 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1038 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 359 .west = true) : bonus 360 p ≤ bonus 359 p := by
  have certified := compare898 p (guard1038 p guard)
  simpa only [at360, at359, Int.zero_add] using certified
theorem check1038 (p : Pattern) : (!walkGuard soko1_2.board support p 360 359 .west || decide (bonus 360 p ≤ bonus 359 p)) = true :=
  check_of_implication _ _ (bound1038 p)
theorem guard1039 (p : Pattern) (guard : pushGuard support p 360 359 358 358 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1039 (p : Pattern) (guard : pushGuard support p 360 359 358 358 = true) : bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some 358)) := by
  have certified := compare1005 p (guard1039 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 359 (some 358))
  have normalized := agree0 _ _ (change_representative support p 359 (some 358) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1039 (p : Pattern) : (!pushGuard support p 360 359 358 358 || decide (bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some 358)))) = true :=
  check_of_implication _ _ (bound1039 p)
theorem guard1040 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 333 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1040 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 333 .northWest = true) : bonus 360 p ≤ bonus 333 p := by
  have certified := compare898 p (guard1040 p guard)
  simpa only [at360, at333, Int.zero_add] using certified
theorem check1040 (p : Pattern) : (!walkGuard soko1_2.board support p 360 333 .northWest || decide (bonus 360 p ≤ bonus 333 p)) = true :=
  check_of_implication _ _ (bound1040 p)
theorem guard1041 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 385 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1041 (p : Pattern) (guard : walkGuard soko1_2.board support p 360 385 .southWest = true) : bonus 360 p ≤ bonus 385 p := by
  have certified := compare898 p (guard1041 p guard)
  simpa only [at360, at385, Int.zero_add] using certified
theorem check1041 (p : Pattern) : (!walkGuard soko1_2.board support p 360 385 .southWest || decide (bonus 360 p ≤ bonus 385 p)) = true :=
  check_of_implication _ _ (bound1041 p)
theorem guard1042 (p : Pattern) (guard : walkGuard soko1_2.board support p 370 396 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1042 (p : Pattern) (guard : walkGuard soko1_2.board support p 370 396 .south = true) : bonus 370 p ≤ bonus 396 p := by
  have certified := compare897 p (guard1042 p guard)
  simpa only [at370, at396, Int.zero_add] using certified
theorem check1042 (p : Pattern) : (!walkGuard soko1_2.board support p 370 396 .south || decide (bonus 370 p ≤ bonus 396 p)) = true :=
  check_of_implication _ _ (bound1042 p)
theorem guard1043 (p : Pattern) (guard : walkGuard soko1_2.board support p 370 371 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1043 (p : Pattern) (guard : walkGuard soko1_2.board support p 370 371 .east = true) : bonus 370 p ≤ bonus 371 p := by
  have certified := compare897 p (guard1043 p guard)
  simpa only [at370, at371, Int.zero_add] using certified
theorem check1043 (p : Pattern) : (!walkGuard soko1_2.board support p 370 371 .east || decide (bonus 370 p ≤ bonus 371 p)) = true :=
  check_of_implication _ _ (bound1043 p)
theorem guard1044 (p : Pattern) (guard : pushGuard support p 370 371 372 372 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1044 (p : Pattern) (guard : pushGuard support p 370 371 372 372 = true) : bonus 370 p ≤ 1 + Generated.soko1_2Potential.boulder 372 - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some 372)) := by
  have certified := compare2570 p (guard1044 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 371 (some 372))
  have normalized := agree258 _ _ (change_representative support p 371 (some 372) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1044 (p : Pattern) : (!pushGuard support p 370 371 372 372 || decide (bonus 370 p ≤ 1 + Generated.soko1_2Potential.boulder 372 - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some 372)))) = true :=
  check_of_implication _ _ (bound1044 p)
theorem guard1045 (p : Pattern) (guard : walkGuard soko1_2.board support p 370 345 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1045 (p : Pattern) (guard : walkGuard soko1_2.board support p 370 345 .northEast = true) : bonus 370 p ≤ bonus 345 p := by
  have certified := compare897 p (guard1045 p guard)
  simpa only [at370, at345, Int.zero_add] using certified
theorem check1045 (p : Pattern) : (!walkGuard soko1_2.board support p 370 345 .northEast || decide (bonus 370 p ≤ bonus 345 p)) = true :=
  check_of_implication _ _ (bound1045 p)
theorem guard1046 (p : Pattern) (guard : walkGuard soko1_2.board support p 370 397 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1046 (p : Pattern) (guard : walkGuard soko1_2.board support p 370 397 .southEast = true) : bonus 370 p ≤ bonus 397 p := by
  have certified := compare897 p (guard1046 p guard)
  simpa only [at370, at397, Int.zero_add] using certified
theorem check1046 (p : Pattern) : (!walkGuard soko1_2.board support p 370 397 .southEast || decide (bonus 370 p ≤ bonus 397 p)) = true :=
  check_of_implication _ _ (bound1046 p)
theorem guard1047 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 345 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1047 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 345 .north = true) : bonus 371 p ≤ bonus 345 p := by
  have certified := compare897 p (guard1047 p guard)
  simpa only [at371, at345, Int.zero_add] using certified
theorem check1047 (p : Pattern) : (!walkGuard soko1_2.board support p 371 345 .north || decide (bonus 371 p ≤ bonus 345 p)) = true :=
  check_of_implication _ _ (bound1047 p)
theorem guard1048 (p : Pattern) (guard : pushGuard support p 371 345 319 319 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1048 (p : Pattern) (guard : pushGuard support p 371 345 319 319 = true) : bonus 371 p ≤ 1 + Generated.soko1_2Potential.boulder 319 - Generated.soko1_2Potential.boulder 345 + bonus 345 (change p 345 (some 319)) := by
  have certified := compare897 p (guard1048 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 345 (some 319))
  have normalized := agree258 _ _ (change_representative support p 345 (some 319) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1048 (p : Pattern) : (!pushGuard support p 371 345 319 319 || decide (bonus 371 p ≤ 1 + Generated.soko1_2Potential.boulder 319 - Generated.soko1_2Potential.boulder 345 + bonus 345 (change p 345 (some 319)))) = true :=
  check_of_implication _ _ (bound1048 p)
theorem guard1049 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 397 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1049 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 397 .south = true) : bonus 371 p ≤ bonus 397 p := by
  have certified := compare897 p (guard1049 p guard)
  simpa only [at371, at397, Int.zero_add] using certified
theorem check1049 (p : Pattern) : (!walkGuard soko1_2.board support p 371 397 .south || decide (bonus 371 p ≤ bonus 397 p)) = true :=
  check_of_implication _ _ (bound1049 p)
theorem guard1050 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 372 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1050 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 372 .east = true) : bonus 371 p ≤ bonus 372 p := by
  have certified := compare897 p (guard1050 p guard)
  simpa only [at371, at372, Int.zero_add] using certified
theorem check1050 (p : Pattern) : (!walkGuard soko1_2.board support p 371 372 .east || decide (bonus 371 p ≤ bonus 372 p)) = true :=
  check_of_implication _ _ (bound1050 p)
theorem guard1051 (p : Pattern) (guard : pushGuard support p 371 372 373 373 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1051 (p : Pattern) (guard : pushGuard support p 371 372 373 373 = true) : bonus 371 p ≤ 1 + Generated.soko1_2Potential.boulder 373 - Generated.soko1_2Potential.boulder 372 + bonus 372 (change p 372 (some 373)) := by
  have certified := compare5431 p (guard1051 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 372 (some 373))
  have normalized := agree258 _ _ (change_representative support p 372 (some 373) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1051 (p : Pattern) : (!pushGuard support p 371 372 373 373 || decide (bonus 371 p ≤ 1 + Generated.soko1_2Potential.boulder 373 - Generated.soko1_2Potential.boulder 372 + bonus 372 (change p 372 (some 373)))) = true :=
  check_of_implication _ _ (bound1051 p)
theorem guard1052 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 370 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1052 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 370 .west = true) : bonus 371 p ≤ bonus 370 p := by
  have certified := compare897 p (guard1052 p guard)
  simpa only [at371, at370, Int.zero_add] using certified
theorem check1052 (p : Pattern) : (!walkGuard soko1_2.board support p 371 370 .west || decide (bonus 371 p ≤ bonus 370 p)) = true :=
  check_of_implication _ _ (bound1052 p)
theorem guard1053 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 396 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1053 (p : Pattern) (guard : walkGuard soko1_2.board support p 371 396 .southWest = true) : bonus 371 p ≤ bonus 396 p := by
  have certified := compare897 p (guard1053 p guard)
  simpa only [at371, at396, Int.zero_add] using certified
theorem check1053 (p : Pattern) : (!walkGuard soko1_2.board support p 371 396 .southWest || decide (bonus 371 p ≤ bonus 396 p)) = true :=
  check_of_implication _ _ (bound1053 p)
theorem guard1054 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 373 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1054 (p : Pattern) (guard : walkGuard soko1_2.board support p 372 373 .east = true) : bonus 372 p ≤ bonus 373 p := by
  have certified := compare897 p (guard1054 p guard)
  simpa only [at372, at373, Int.zero_add] using certified
theorem check1054 (p : Pattern) : (!walkGuard soko1_2.board support p 372 373 .east || decide (bonus 372 p ≤ bonus 373 p)) = true :=
  check_of_implication _ _ (bound1054 p)
theorem guard1055 (p : Pattern) (guard : pushGuard support p 372 373 374 374 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1055 (p : Pattern) (guard : pushGuard support p 372 373 374 374 = true) : bonus 372 p ≤ 1 + Generated.soko1_2Potential.boulder 374 - Generated.soko1_2Potential.boulder 373 + bonus 373 (change p 373 (some 374)) := by
  have certified := compare5431 p (guard1055 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 373 (some 374))
  have normalized := agree258 _ _ (change_representative support p 373 (some 374) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check1055 (p : Pattern) : (!pushGuard support p 372 373 374 374 || decide (bonus 372 p ≤ 1 + Generated.soko1_2Potential.boulder 374 - Generated.soko1_2Potential.boulder 373 + bonus 373 (change p 373 (some 374)))) = true :=
  check_of_implication _ _ (bound1055 p)
end NetHack.Sokoban12CostPartition
