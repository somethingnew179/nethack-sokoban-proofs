import NetHack.Sokoban12CostPartition.ActionBounds041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1008 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 330 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1008 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 330 .northWest = true) : bonus 357 p ≤ bonus 330 p := by
  have certified := compare898 p (guard1008 p guard)
  simpa only [at357, at330, Int.zero_add] using certified
theorem check1008 (p : Pattern) : (!walkGuard soko1_2.board support p 357 330 .northWest || decide (bonus 357 p ≤ bonus 330 p)) = true :=
  check_of_implication _ _ (bound1008 p)
theorem guard1009 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 384 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1009 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 384 .southEast = true) : bonus 357 p ≤ bonus 384 p := by
  have certified := compare898 p (guard1009 p guard)
  simpa only [at357, at384, Int.zero_add] using certified
theorem check1009 (p : Pattern) : (!walkGuard soko1_2.board support p 357 384 .southEast || decide (bonus 357 p ≤ bonus 384 p)) = true :=
  check_of_implication _ _ (bound1009 p)
theorem guard1010 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 382 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1010 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 382 .southWest = true) : bonus 357 p ≤ bonus 382 p := by
  have certified := compare898 p (guard1010 p guard)
  simpa only [at357, at382, Int.zero_add] using certified
theorem check1010 (p : Pattern) : (!walkGuard soko1_2.board support p 357 382 .southWest || decide (bonus 357 p ≤ bonus 382 p)) = true :=
  check_of_implication _ _ (bound1010 p)
theorem guard1011 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 332 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1011 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 332 .north = true) : bonus 358 p ≤ bonus 332 p := by
  have certified := compare898 p (guard1011 p guard)
  simpa only [at358, at332, Int.zero_add] using certified
theorem check1011 (p : Pattern) : (!walkGuard soko1_2.board support p 358 332 .north || decide (bonus 358 p ≤ bonus 332 p)) = true :=
  check_of_implication _ _ (bound1011 p)
theorem guard1012 (p : Pattern) (guard : pushGuard support p 358 332 306 306 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1012 (p : Pattern) (guard : pushGuard support p 358 332 306 306 = true) : bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some 306)) := by
  have certified := compare1005 p (guard1012 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 332 (some 306))
  have normalized := agree0 _ _ (change_representative support p 332 (some 306) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1012 (p : Pattern) : (!pushGuard support p 358 332 306 306 || decide (bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some 306)))) = true :=
  check_of_implication _ _ (bound1012 p)
theorem guard1013 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 384 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1013 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 384 .south = true) : bonus 358 p ≤ bonus 384 p := by
  have certified := compare898 p (guard1013 p guard)
  simpa only [at358, at384, Int.zero_add] using certified
theorem check1013 (p : Pattern) : (!walkGuard soko1_2.board support p 358 384 .south || decide (bonus 358 p ≤ bonus 384 p)) = true :=
  check_of_implication _ _ (bound1013 p)
theorem guard1014 (p : Pattern) (guard : pushGuard support p 358 384 410 410 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1014 (p : Pattern) (guard : pushGuard support p 358 384 410 410 = true) : bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder 410 - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some 410)) := by
  have certified := compare1005 p (guard1014 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 384 (some 410))
  have normalized := agree0 _ _ (change_representative support p 384 (some 410) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1014 (p : Pattern) : (!pushGuard support p 358 384 410 410 || decide (bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder 410 - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some 410)))) = true :=
  check_of_implication _ _ (bound1014 p)
theorem guard1015 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 359 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1015 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 359 .east = true) : bonus 358 p ≤ bonus 359 p := by
  have certified := compare898 p (guard1015 p guard)
  simpa only [at358, at359, Int.zero_add] using certified
theorem check1015 (p : Pattern) : (!walkGuard soko1_2.board support p 358 359 .east || decide (bonus 358 p ≤ bonus 359 p)) = true :=
  check_of_implication _ _ (bound1015 p)
theorem guard1016 (p : Pattern) (guard : pushGuard support p 358 359 360 360 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1016 (p : Pattern) (guard : pushGuard support p 358 359 360 360 = true) : bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder 360 - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some 360)) := by
  have certified := compare1005 p (guard1016 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 359 (some 360))
  have normalized := agree0 _ _ (change_representative support p 359 (some 360) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1016 (p : Pattern) : (!pushGuard support p 358 359 360 360 || decide (bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder 360 - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some 360)))) = true :=
  check_of_implication _ _ (bound1016 p)
theorem guard1017 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 357 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1017 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 357 .west = true) : bonus 358 p ≤ bonus 357 p := by
  have certified := compare898 p (guard1017 p guard)
  simpa only [at358, at357, Int.zero_add] using certified
theorem check1017 (p : Pattern) : (!walkGuard soko1_2.board support p 358 357 .west || decide (bonus 358 p ≤ bonus 357 p)) = true :=
  check_of_implication _ _ (bound1017 p)
theorem guard1018 (p : Pattern) (guard : pushGuard support p 358 357 356 356 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1018 (p : Pattern) (guard : pushGuard support p 358 357 356 356 = true) : bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder 356 - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some 356)) := by
  have certified := compare1005 p (guard1018 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 357 (some 356))
  have normalized := agree0 _ _ (change_representative support p 357 (some 356) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1018 (p : Pattern) : (!pushGuard support p 358 357 356 356 || decide (bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder 356 - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some 356)))) = true :=
  check_of_implication _ _ (bound1018 p)
theorem guard1019 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 333 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1019 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 333 .northEast = true) : bonus 358 p ≤ bonus 333 p := by
  have certified := compare898 p (guard1019 p guard)
  simpa only [at358, at333, Int.zero_add] using certified
theorem check1019 (p : Pattern) : (!walkGuard soko1_2.board support p 358 333 .northEast || decide (bonus 358 p ≤ bonus 333 p)) = true :=
  check_of_implication _ _ (bound1019 p)
theorem guard1020 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 331 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1020 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 331 .northWest = true) : bonus 358 p ≤ bonus 331 p := by
  have certified := compare898 p (guard1020 p guard)
  simpa only [at358, at331, Int.zero_add] using certified
theorem check1020 (p : Pattern) : (!walkGuard soko1_2.board support p 358 331 .northWest || decide (bonus 358 p ≤ bonus 331 p)) = true :=
  check_of_implication _ _ (bound1020 p)
theorem guard1021 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 385 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1021 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 385 .southEast = true) : bonus 358 p ≤ bonus 385 p := by
  have certified := compare898 p (guard1021 p guard)
  simpa only [at358, at385, Int.zero_add] using certified
theorem check1021 (p : Pattern) : (!walkGuard soko1_2.board support p 358 385 .southEast || decide (bonus 358 p ≤ bonus 385 p)) = true :=
  check_of_implication _ _ (bound1021 p)
theorem guard1022 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 383 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1022 (p : Pattern) (guard : walkGuard soko1_2.board support p 358 383 .southWest = true) : bonus 358 p ≤ bonus 383 p := by
  have certified := compare898 p (guard1022 p guard)
  simpa only [at358, at383, Int.zero_add] using certified
theorem check1022 (p : Pattern) : (!walkGuard soko1_2.board support p 358 383 .southWest || decide (bonus 358 p ≤ bonus 383 p)) = true :=
  check_of_implication _ _ (bound1022 p)
theorem guard1023 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 333 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1023 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 333 .north = true) : bonus 359 p ≤ bonus 333 p := by
  have certified := compare898 p (guard1023 p guard)
  simpa only [at359, at333, Int.zero_add] using certified
theorem check1023 (p : Pattern) : (!walkGuard soko1_2.board support p 359 333 .north || decide (bonus 359 p ≤ bonus 333 p)) = true :=
  check_of_implication _ _ (bound1023 p)
theorem guard1024 (p : Pattern) (guard : pushGuard support p 359 333 307 307 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1024 (p : Pattern) (guard : pushGuard support p 359 333 307 307 = true) : bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some 307)) := by
  have certified := compare1005 p (guard1024 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 333 (some 307))
  have normalized := agree0 _ _ (change_representative support p 333 (some 307) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1024 (p : Pattern) : (!pushGuard support p 359 333 307 307 || decide (bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some 307)))) = true :=
  check_of_implication _ _ (bound1024 p)
theorem guard1025 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 385 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1025 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 385 .south = true) : bonus 359 p ≤ bonus 385 p := by
  have certified := compare898 p (guard1025 p guard)
  simpa only [at359, at385, Int.zero_add] using certified
theorem check1025 (p : Pattern) : (!walkGuard soko1_2.board support p 359 385 .south || decide (bonus 359 p ≤ bonus 385 p)) = true :=
  check_of_implication _ _ (bound1025 p)
theorem guard1026 (p : Pattern) (guard : pushGuard support p 359 385 411 411 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1026 (p : Pattern) (guard : pushGuard support p 359 385 411 411 = true) : bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder 411 - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some 411)) := by
  have certified := compare1005 p (guard1026 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 385 (some 411))
  have normalized := agree0 _ _ (change_representative support p 385 (some 411) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1026 (p : Pattern) : (!pushGuard support p 359 385 411 411 || decide (bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder 411 - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some 411)))) = true :=
  check_of_implication _ _ (bound1026 p)
theorem guard1027 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 360 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1027 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 360 .east = true) : bonus 359 p ≤ bonus 360 p := by
  have certified := compare898 p (guard1027 p guard)
  simpa only [at359, at360, Int.zero_add] using certified
theorem check1027 (p : Pattern) : (!walkGuard soko1_2.board support p 359 360 .east || decide (bonus 359 p ≤ bonus 360 p)) = true :=
  check_of_implication _ _ (bound1027 p)
theorem guard1028 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 358 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1028 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 358 .west = true) : bonus 359 p ≤ bonus 358 p := by
  have certified := compare898 p (guard1028 p guard)
  simpa only [at359, at358, Int.zero_add] using certified
theorem check1028 (p : Pattern) : (!walkGuard soko1_2.board support p 359 358 .west || decide (bonus 359 p ≤ bonus 358 p)) = true :=
  check_of_implication _ _ (bound1028 p)
theorem guard1029 (p : Pattern) (guard : pushGuard support p 359 358 357 357 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1029 (p : Pattern) (guard : pushGuard support p 359 358 357 357 = true) : bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some 357)) := by
  have certified := compare1005 p (guard1029 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 358 (some 357))
  have normalized := agree0 _ _ (change_representative support p 358 (some 357) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1029 (p : Pattern) : (!pushGuard support p 359 358 357 357 || decide (bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some 357)))) = true :=
  check_of_implication _ _ (bound1029 p)
theorem guard1030 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 334 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1030 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 334 .northEast = true) : bonus 359 p ≤ bonus 334 p := by
  have certified := compare898 p (guard1030 p guard)
  simpa only [at359, at334, Int.zero_add] using certified
theorem check1030 (p : Pattern) : (!walkGuard soko1_2.board support p 359 334 .northEast || decide (bonus 359 p ≤ bonus 334 p)) = true :=
  check_of_implication _ _ (bound1030 p)
theorem guard1031 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 332 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1031 (p : Pattern) (guard : walkGuard soko1_2.board support p 359 332 .northWest = true) : bonus 359 p ≤ bonus 332 p := by
  have certified := compare898 p (guard1031 p guard)
  simpa only [at359, at332, Int.zero_add] using certified
theorem check1031 (p : Pattern) : (!walkGuard soko1_2.board support p 359 332 .northWest || decide (bonus 359 p ≤ bonus 332 p)) = true :=
  check_of_implication _ _ (bound1031 p)
end NetHack.Sokoban12CostPartition
