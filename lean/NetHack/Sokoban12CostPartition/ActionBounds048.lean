import NetHack.Sokoban12CostPartition.ActionBounds047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1152 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 385 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1152 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 385 .northEast = true) : bonus 410 p ≤ bonus 385 p := by
  have certified := compare898 p (guard1152 p guard)
  simpa only [at410, at385, Int.zero_add] using certified
theorem check1152 (p : Pattern) : (!walkGuard soko1_2.board support p 410 385 .northEast || decide (bonus 410 p ≤ bonus 385 p)) = true :=
  check_of_implication _ _ (bound1152 p)
theorem guard1153 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 383 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1153 (p : Pattern) (guard : walkGuard soko1_2.board support p 410 383 .northWest = true) : bonus 410 p ≤ bonus 383 p := by
  have certified := compare898 p (guard1153 p guard)
  simpa only [at410, at383, Int.zero_add] using certified
theorem check1153 (p : Pattern) : (!walkGuard soko1_2.board support p 410 383 .northWest || decide (bonus 410 p ≤ bonus 383 p)) = true :=
  check_of_implication _ _ (bound1153 p)
theorem guard1154 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 385 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1154 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 385 .north = true) : bonus 411 p ≤ bonus 385 p := by
  have certified := compare898 p (guard1154 p guard)
  simpa only [at411, at385, Int.zero_add] using certified
theorem check1154 (p : Pattern) : (!walkGuard soko1_2.board support p 411 385 .north || decide (bonus 411 p ≤ bonus 385 p)) = true :=
  check_of_implication _ _ (bound1154 p)
theorem guard1155 (p : Pattern) (guard : pushGuard support p 411 385 359 359 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1155 (p : Pattern) (guard : pushGuard support p 411 385 359 359 = true) : bonus 411 p ≤ 1 + Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some 359)) := by
  have certified := compare1005 p (guard1155 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 385 (some 359))
  have normalized := agree0 _ _ (change_representative support p 385 (some 359) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1155 (p : Pattern) : (!pushGuard support p 411 385 359 359 || decide (bonus 411 p ≤ 1 + Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some 359)))) = true :=
  check_of_implication _ _ (bound1155 p)
theorem guard1156 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 412 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1156 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 412 .east = true) : bonus 411 p ≤ bonus 412 p := by
  have certified := compare898 p (guard1156 p guard)
  simpa only [at411, at412, Int.zero_add] using certified
theorem check1156 (p : Pattern) : (!walkGuard soko1_2.board support p 411 412 .east || decide (bonus 411 p ≤ bonus 412 p)) = true :=
  check_of_implication _ _ (bound1156 p)
theorem guard1157 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 410 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1157 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 410 .west = true) : bonus 411 p ≤ bonus 410 p := by
  have certified := compare898 p (guard1157 p guard)
  simpa only [at411, at410, Int.zero_add] using certified
theorem check1157 (p : Pattern) : (!walkGuard soko1_2.board support p 411 410 .west || decide (bonus 411 p ≤ bonus 410 p)) = true :=
  check_of_implication _ _ (bound1157 p)
theorem guard1158 (p : Pattern) (guard : pushGuard support p 411 410 409 409 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1158 (p : Pattern) (guard : pushGuard support p 411 410 409 409 = true) : bonus 411 p ≤ 1 + Generated.soko1_2Potential.boulder 409 - Generated.soko1_2Potential.boulder 410 + bonus 410 (change p 410 (some 409)) := by
  have certified := compare1005 p (guard1158 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 410 (some 409))
  have normalized := agree0 _ _ (change_representative support p 410 (some 409) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1158 (p : Pattern) : (!pushGuard support p 411 410 409 409 || decide (bonus 411 p ≤ 1 + Generated.soko1_2Potential.boulder 409 - Generated.soko1_2Potential.boulder 410 + bonus 410 (change p 410 (some 409)))) = true :=
  check_of_implication _ _ (bound1158 p)
theorem guard1159 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 386 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1159 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 386 .northEast = true) : bonus 411 p ≤ bonus 386 p := by
  have certified := compare898 p (guard1159 p guard)
  simpa only [at411, at386, Int.zero_add] using certified
theorem check1159 (p : Pattern) : (!walkGuard soko1_2.board support p 411 386 .northEast || decide (bonus 411 p ≤ bonus 386 p)) = true :=
  check_of_implication _ _ (bound1159 p)
theorem guard1160 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 384 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1160 (p : Pattern) (guard : walkGuard soko1_2.board support p 411 384 .northWest = true) : bonus 411 p ≤ bonus 384 p := by
  have certified := compare898 p (guard1160 p guard)
  simpa only [at411, at384, Int.zero_add] using certified
theorem check1160 (p : Pattern) : (!walkGuard soko1_2.board support p 411 384 .northWest || decide (bonus 411 p ≤ bonus 384 p)) = true :=
  check_of_implication _ _ (bound1160 p)
theorem guard1161 (p : Pattern) (guard : walkGuard soko1_2.board support p 412 386 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1161 (p : Pattern) (guard : walkGuard soko1_2.board support p 412 386 .north = true) : bonus 412 p ≤ bonus 386 p := by
  have certified := compare898 p (guard1161 p guard)
  simpa only [at412, at386, Int.zero_add] using certified
theorem check1161 (p : Pattern) : (!walkGuard soko1_2.board support p 412 386 .north || decide (bonus 412 p ≤ bonus 386 p)) = true :=
  check_of_implication _ _ (bound1161 p)
theorem guard1162 (p : Pattern) (guard : pushGuard support p 412 386 360 360 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1162 (p : Pattern) (guard : pushGuard support p 412 386 360 360 = true) : bonus 412 p ≤ 1 + Generated.soko1_2Potential.boulder 360 - Generated.soko1_2Potential.boulder 386 + bonus 386 (change p 386 (some 360)) := by
  have certified := compare1005 p (guard1162 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 386 (some 360))
  have normalized := agree0 _ _ (change_representative support p 386 (some 360) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1162 (p : Pattern) : (!pushGuard support p 412 386 360 360 || decide (bonus 412 p ≤ 1 + Generated.soko1_2Potential.boulder 360 - Generated.soko1_2Potential.boulder 386 + bonus 386 (change p 386 (some 360)))) = true :=
  check_of_implication _ _ (bound1162 p)
theorem guard1163 (p : Pattern) (guard : walkGuard soko1_2.board support p 412 411 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1163 (p : Pattern) (guard : walkGuard soko1_2.board support p 412 411 .west = true) : bonus 412 p ≤ bonus 411 p := by
  have certified := compare898 p (guard1163 p guard)
  simpa only [at412, at411, Int.zero_add] using certified
theorem check1163 (p : Pattern) : (!walkGuard soko1_2.board support p 412 411 .west || decide (bonus 412 p ≤ bonus 411 p)) = true :=
  check_of_implication _ _ (bound1163 p)
theorem guard1164 (p : Pattern) (guard : pushGuard support p 412 411 410 410 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1164 (p : Pattern) (guard : pushGuard support p 412 411 410 410 = true) : bonus 412 p ≤ 1 + Generated.soko1_2Potential.boulder 410 - Generated.soko1_2Potential.boulder 411 + bonus 411 (change p 411 (some 410)) := by
  have certified := compare1005 p (guard1164 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 411 (some 410))
  have normalized := agree0 _ _ (change_representative support p 411 (some 410) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1164 (p : Pattern) : (!pushGuard support p 412 411 410 410 || decide (bonus 412 p ≤ 1 + Generated.soko1_2Potential.boulder 410 - Generated.soko1_2Potential.boulder 411 + bonus 411 (change p 411 (some 410)))) = true :=
  check_of_implication _ _ (bound1164 p)
theorem guard1165 (p : Pattern) (guard : walkGuard soko1_2.board support p 412 385 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1165 (p : Pattern) (guard : walkGuard soko1_2.board support p 412 385 .northWest = true) : bonus 412 p ≤ bonus 385 p := by
  have certified := compare898 p (guard1165 p guard)
  simpa only [at412, at385, Int.zero_add] using certified
theorem check1165 (p : Pattern) : (!walkGuard soko1_2.board support p 412 385 .northWest || decide (bonus 412 p ≤ bonus 385 p)) = true :=
  check_of_implication _ _ (bound1165 p)
end NetHack.Sokoban12CostPartition
