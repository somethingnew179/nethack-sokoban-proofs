import NetHack.Sokoban12CostPartition.ActionBounds044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1080 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 357 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1080 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 357 .north = true) : bonus 383 p ≤ bonus 357 p := by
  have certified := compare898 p (guard1080 p guard)
  simpa only [at383, at357, Int.zero_add] using certified
theorem check1080 (p : Pattern) : (!walkGuard soko1_2.board support p 383 357 .north || decide (bonus 383 p ≤ bonus 357 p)) = true :=
  check_of_implication _ _ (bound1080 p)
theorem guard1081 (p : Pattern) (guard : pushGuard support p 383 357 331 331 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1081 (p : Pattern) (guard : pushGuard support p 383 357 331 331 = true) : bonus 383 p ≤ 1 + Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some 331)) := by
  have certified := compare1005 p (guard1081 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 357 (some 331))
  have normalized := agree0 _ _ (change_representative support p 357 (some 331) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1081 (p : Pattern) : (!pushGuard support p 383 357 331 331 || decide (bonus 383 p ≤ 1 + Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some 331)))) = true :=
  check_of_implication _ _ (bound1081 p)
theorem guard1082 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 409 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1082 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 409 .south = true) : bonus 383 p ≤ bonus 409 p := by
  have certified := compare898 p (guard1082 p guard)
  simpa only [at383, at409, Int.zero_add] using certified
theorem check1082 (p : Pattern) : (!walkGuard soko1_2.board support p 383 409 .south || decide (bonus 383 p ≤ bonus 409 p)) = true :=
  check_of_implication _ _ (bound1082 p)
theorem guard1083 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 384 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1083 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 384 .east = true) : bonus 383 p ≤ bonus 384 p := by
  have certified := compare898 p (guard1083 p guard)
  simpa only [at383, at384, Int.zero_add] using certified
theorem check1083 (p : Pattern) : (!walkGuard soko1_2.board support p 383 384 .east || decide (bonus 383 p ≤ bonus 384 p)) = true :=
  check_of_implication _ _ (bound1083 p)
theorem guard1084 (p : Pattern) (guard : pushGuard support p 383 384 385 385 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1084 (p : Pattern) (guard : pushGuard support p 383 384 385 385 = true) : bonus 383 p ≤ 1 + Generated.soko1_2Potential.boulder 385 - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some 385)) := by
  have certified := compare1005 p (guard1084 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 384 (some 385))
  have normalized := agree0 _ _ (change_representative support p 384 (some 385) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1084 (p : Pattern) : (!pushGuard support p 383 384 385 385 || decide (bonus 383 p ≤ 1 + Generated.soko1_2Potential.boulder 385 - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some 385)))) = true :=
  check_of_implication _ _ (bound1084 p)
theorem guard1085 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 382 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1085 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 382 .west = true) : bonus 383 p ≤ bonus 382 p := by
  have certified := compare898 p (guard1085 p guard)
  simpa only [at383, at382, Int.zero_add] using certified
theorem check1085 (p : Pattern) : (!walkGuard soko1_2.board support p 383 382 .west || decide (bonus 383 p ≤ bonus 382 p)) = true :=
  check_of_implication _ _ (bound1085 p)
theorem guard1086 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 358 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1086 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 358 .northEast = true) : bonus 383 p ≤ bonus 358 p := by
  have certified := compare898 p (guard1086 p guard)
  simpa only [at383, at358, Int.zero_add] using certified
theorem check1086 (p : Pattern) : (!walkGuard soko1_2.board support p 383 358 .northEast || decide (bonus 383 p ≤ bonus 358 p)) = true :=
  check_of_implication _ _ (bound1086 p)
theorem guard1087 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 356 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1087 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 356 .northWest = true) : bonus 383 p ≤ bonus 356 p := by
  have certified := compare898 p (guard1087 p guard)
  simpa only [at383, at356, Int.zero_add] using certified
theorem check1087 (p : Pattern) : (!walkGuard soko1_2.board support p 383 356 .northWest || decide (bonus 383 p ≤ bonus 356 p)) = true :=
  check_of_implication _ _ (bound1087 p)
theorem guard1088 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 410 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1088 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 410 .southEast = true) : bonus 383 p ≤ bonus 410 p := by
  have certified := compare898 p (guard1088 p guard)
  simpa only [at383, at410, Int.zero_add] using certified
theorem check1088 (p : Pattern) : (!walkGuard soko1_2.board support p 383 410 .southEast || decide (bonus 383 p ≤ bonus 410 p)) = true :=
  check_of_implication _ _ (bound1088 p)
theorem guard1089 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 408 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1089 (p : Pattern) (guard : walkGuard soko1_2.board support p 383 408 .southWest = true) : bonus 383 p ≤ bonus 408 p := by
  have certified := compare898 p (guard1089 p guard)
  simpa only [at383, at408, Int.zero_add] using certified
theorem check1089 (p : Pattern) : (!walkGuard soko1_2.board support p 383 408 .southWest || decide (bonus 383 p ≤ bonus 408 p)) = true :=
  check_of_implication _ _ (bound1089 p)
theorem guard1090 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 358 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1090 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 358 .north = true) : bonus 384 p ≤ bonus 358 p := by
  have certified := compare898 p (guard1090 p guard)
  simpa only [at384, at358, Int.zero_add] using certified
theorem check1090 (p : Pattern) : (!walkGuard soko1_2.board support p 384 358 .north || decide (bonus 384 p ≤ bonus 358 p)) = true :=
  check_of_implication _ _ (bound1090 p)
theorem guard1091 (p : Pattern) (guard : pushGuard support p 384 358 332 332 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1091 (p : Pattern) (guard : pushGuard support p 384 358 332 332 = true) : bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some 332)) := by
  have certified := compare1005 p (guard1091 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 358 (some 332))
  have normalized := agree0 _ _ (change_representative support p 358 (some 332) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1091 (p : Pattern) : (!pushGuard support p 384 358 332 332 || decide (bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some 332)))) = true :=
  check_of_implication _ _ (bound1091 p)
theorem guard1092 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 410 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1092 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 410 .south = true) : bonus 384 p ≤ bonus 410 p := by
  have certified := compare898 p (guard1092 p guard)
  simpa only [at384, at410, Int.zero_add] using certified
theorem check1092 (p : Pattern) : (!walkGuard soko1_2.board support p 384 410 .south || decide (bonus 384 p ≤ bonus 410 p)) = true :=
  check_of_implication _ _ (bound1092 p)
theorem guard1093 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 385 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1093 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 385 .east = true) : bonus 384 p ≤ bonus 385 p := by
  have certified := compare898 p (guard1093 p guard)
  simpa only [at384, at385, Int.zero_add] using certified
theorem check1093 (p : Pattern) : (!walkGuard soko1_2.board support p 384 385 .east || decide (bonus 384 p ≤ bonus 385 p)) = true :=
  check_of_implication _ _ (bound1093 p)
theorem guard1094 (p : Pattern) (guard : pushGuard support p 384 385 386 386 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1094 (p : Pattern) (guard : pushGuard support p 384 385 386 386 = true) : bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder 386 - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some 386)) := by
  have certified := compare1005 p (guard1094 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 385 (some 386))
  have normalized := agree0 _ _ (change_representative support p 385 (some 386) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1094 (p : Pattern) : (!pushGuard support p 384 385 386 386 || decide (bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder 386 - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some 386)))) = true :=
  check_of_implication _ _ (bound1094 p)
theorem guard1095 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 383 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1095 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 383 .west = true) : bonus 384 p ≤ bonus 383 p := by
  have certified := compare898 p (guard1095 p guard)
  simpa only [at384, at383, Int.zero_add] using certified
theorem check1095 (p : Pattern) : (!walkGuard soko1_2.board support p 384 383 .west || decide (bonus 384 p ≤ bonus 383 p)) = true :=
  check_of_implication _ _ (bound1095 p)
theorem guard1096 (p : Pattern) (guard : pushGuard support p 384 383 382 382 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1096 (p : Pattern) (guard : pushGuard support p 384 383 382 382 = true) : bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder 382 - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some 382)) := by
  have certified := compare1005 p (guard1096 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 383 (some 382))
  have normalized := agree0 _ _ (change_representative support p 383 (some 382) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1096 (p : Pattern) : (!pushGuard support p 384 383 382 382 || decide (bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder 382 - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some 382)))) = true :=
  check_of_implication _ _ (bound1096 p)
theorem guard1097 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 359 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1097 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 359 .northEast = true) : bonus 384 p ≤ bonus 359 p := by
  have certified := compare898 p (guard1097 p guard)
  simpa only [at384, at359, Int.zero_add] using certified
theorem check1097 (p : Pattern) : (!walkGuard soko1_2.board support p 384 359 .northEast || decide (bonus 384 p ≤ bonus 359 p)) = true :=
  check_of_implication _ _ (bound1097 p)
theorem guard1098 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 357 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1098 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 357 .northWest = true) : bonus 384 p ≤ bonus 357 p := by
  have certified := compare898 p (guard1098 p guard)
  simpa only [at384, at357, Int.zero_add] using certified
theorem check1098 (p : Pattern) : (!walkGuard soko1_2.board support p 384 357 .northWest || decide (bonus 384 p ≤ bonus 357 p)) = true :=
  check_of_implication _ _ (bound1098 p)
theorem guard1099 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 411 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1099 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 411 .southEast = true) : bonus 384 p ≤ bonus 411 p := by
  have certified := compare898 p (guard1099 p guard)
  simpa only [at384, at411, Int.zero_add] using certified
theorem check1099 (p : Pattern) : (!walkGuard soko1_2.board support p 384 411 .southEast || decide (bonus 384 p ≤ bonus 411 p)) = true :=
  check_of_implication _ _ (bound1099 p)
theorem guard1100 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 409 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1100 (p : Pattern) (guard : walkGuard soko1_2.board support p 384 409 .southWest = true) : bonus 384 p ≤ bonus 409 p := by
  have certified := compare898 p (guard1100 p guard)
  simpa only [at384, at409, Int.zero_add] using certified
theorem check1100 (p : Pattern) : (!walkGuard soko1_2.board support p 384 409 .southWest || decide (bonus 384 p ≤ bonus 409 p)) = true :=
  check_of_implication _ _ (bound1100 p)
theorem guard1101 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 359 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1101 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 359 .north = true) : bonus 385 p ≤ bonus 359 p := by
  have certified := compare898 p (guard1101 p guard)
  simpa only [at385, at359, Int.zero_add] using certified
theorem check1101 (p : Pattern) : (!walkGuard soko1_2.board support p 385 359 .north || decide (bonus 385 p ≤ bonus 359 p)) = true :=
  check_of_implication _ _ (bound1101 p)
theorem guard1102 (p : Pattern) (guard : pushGuard support p 385 359 333 333 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1102 (p : Pattern) (guard : pushGuard support p 385 359 333 333 = true) : bonus 385 p ≤ 1 + Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some 333)) := by
  have certified := compare1005 p (guard1102 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 359 (some 333))
  have normalized := agree0 _ _ (change_representative support p 359 (some 333) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1102 (p : Pattern) : (!pushGuard support p 385 359 333 333 || decide (bonus 385 p ≤ 1 + Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some 333)))) = true :=
  check_of_implication _ _ (bound1102 p)
theorem guard1103 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 411 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1103 (p : Pattern) (guard : walkGuard soko1_2.board support p 385 411 .south = true) : bonus 385 p ≤ bonus 411 p := by
  have certified := compare898 p (guard1103 p guard)
  simpa only [at385, at411, Int.zero_add] using certified
theorem check1103 (p : Pattern) : (!walkGuard soko1_2.board support p 385 411 .south || decide (bonus 385 p ≤ bonus 411 p)) = true :=
  check_of_implication _ _ (bound1103 p)
end NetHack.Sokoban12CostPartition
