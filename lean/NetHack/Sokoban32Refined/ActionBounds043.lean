import NetHack.Sokoban32Refined.ActionBounds042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1032 (p : Pattern) (guard : pushGuard support p 228 229 230 230 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1032 (p : Pattern) (guard : pushGuard support p 228 229 230 230 = true) : bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder 230 - Generated.soko3_2Potential.boulder 229 + bonus 229 (change p 229 (some 230)) := by
  have certified := compare37 p (guard1032 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 229 (some 230))
  have normalized := agree0 _ _ (change_representative support p 229 (some 230) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1032 (p : Pattern) : (!pushGuard support p 228 229 230 230 || decide (bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder 230 - Generated.soko3_2Potential.boulder 229 + bonus 229 (change p 229 (some 230)))) = true :=
  check_of_implication _ _ (bound1032 p)
theorem guard1033 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 227 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1033 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 227 .west = true) : bonus 228 p ≤ bonus 227 p := by
  have certified := compare103 p (guard1033 p guard)
  simpa only [at228, at227, Int.zero_add] using certified
theorem check1033 (p : Pattern) : (!walkGuard soko3_2.board support p 228 227 .west || decide (bonus 228 p ≤ bonus 227 p)) = true :=
  check_of_implication _ _ (bound1033 p)
theorem guard1034 (p : Pattern) (guard : pushGuard support p 228 227 226 226 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1034 (p : Pattern) (guard : pushGuard support p 228 227 226 226 = true) : bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder 226 - Generated.soko3_2Potential.boulder 227 + bonus 227 (change p 227 (some 226)) := by
  have certified := compare37 p (guard1034 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 227 (some 226))
  have normalized := agree0 _ _ (change_representative support p 227 (some 226) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1034 (p : Pattern) : (!pushGuard support p 228 227 226 226 || decide (bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder 226 - Generated.soko3_2Potential.boulder 227 + bonus 227 (change p 227 (some 226)))) = true :=
  check_of_implication _ _ (bound1034 p)
theorem guard1035 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 203 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1035 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 203 .northEast = true) : bonus 228 p ≤ bonus 203 p := by
  have certified := compare103 p (guard1035 p guard)
  simpa only [at228, at203, Int.zero_add] using certified
theorem check1035 (p : Pattern) : (!walkGuard soko3_2.board support p 228 203 .northEast || decide (bonus 228 p ≤ bonus 203 p)) = true :=
  check_of_implication _ _ (bound1035 p)
theorem guard1036 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 201 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1036 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 201 .northWest = true) : bonus 228 p ≤ bonus 201 p := by
  have certified := compare103 p (guard1036 p guard)
  simpa only [at228, at201, Int.zero_add] using certified
theorem check1036 (p : Pattern) : (!walkGuard soko3_2.board support p 228 201 .northWest || decide (bonus 228 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound1036 p)
theorem guard1037 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 203 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1037 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 203 .north = true) : bonus 229 p ≤ bonus 203 p := by
  have certified := compare103 p (guard1037 p guard)
  simpa only [at229, at203, Int.zero_add] using certified
theorem check1037 (p : Pattern) : (!walkGuard soko3_2.board support p 229 203 .north || decide (bonus 229 p ≤ bonus 203 p)) = true :=
  check_of_implication _ _ (bound1037 p)
theorem guard1038 (p : Pattern) (guard : pushGuard support p 229 203 177 177 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1038 (p : Pattern) (guard : pushGuard support p 229 203 177 177 = true) : bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some 177)) := by
  have certified := compare37 p (guard1038 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 203 (some 177))
  have normalized := agree0 _ _ (change_representative support p 203 (some 177) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1038 (p : Pattern) : (!pushGuard support p 229 203 177 177 || decide (bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some 177)))) = true :=
  check_of_implication _ _ (bound1038 p)
theorem guard1039 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 230 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1039 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 230 .east = true) : bonus 229 p ≤ bonus 230 p := by
  have certified := compare103 p (guard1039 p guard)
  simpa only [at229, at230, Int.zero_add] using certified
theorem check1039 (p : Pattern) : (!walkGuard soko3_2.board support p 229 230 .east || decide (bonus 229 p ≤ bonus 230 p)) = true :=
  check_of_implication _ _ (bound1039 p)
theorem guard1040 (p : Pattern) (guard : pushGuard support p 229 230 231 231 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1040 (p : Pattern) (guard : pushGuard support p 229 230 231 231 = true) : bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder 231 - Generated.soko3_2Potential.boulder 230 + bonus 230 (change p 230 (some 231)) := by
  have certified := compare37 p (guard1040 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 230 (some 231))
  have normalized := agree0 _ _ (change_representative support p 230 (some 231) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1040 (p : Pattern) : (!pushGuard support p 229 230 231 231 || decide (bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder 231 - Generated.soko3_2Potential.boulder 230 + bonus 230 (change p 230 (some 231)))) = true :=
  check_of_implication _ _ (bound1040 p)
theorem guard1041 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 228 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1041 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 228 .west = true) : bonus 229 p ≤ bonus 228 p := by
  have certified := compare103 p (guard1041 p guard)
  simpa only [at229, at228, Int.zero_add] using certified
theorem check1041 (p : Pattern) : (!walkGuard soko3_2.board support p 229 228 .west || decide (bonus 229 p ≤ bonus 228 p)) = true :=
  check_of_implication _ _ (bound1041 p)
theorem guard1042 (p : Pattern) (guard : pushGuard support p 229 228 227 227 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1042 (p : Pattern) (guard : pushGuard support p 229 228 227 227 = true) : bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder 227 - Generated.soko3_2Potential.boulder 228 + bonus 228 (change p 228 (some 227)) := by
  have certified := compare37 p (guard1042 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 228 (some 227))
  have normalized := agree0 _ _ (change_representative support p 228 (some 227) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1042 (p : Pattern) : (!pushGuard support p 229 228 227 227 || decide (bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder 227 - Generated.soko3_2Potential.boulder 228 + bonus 228 (change p 228 (some 227)))) = true :=
  check_of_implication _ _ (bound1042 p)
theorem guard1043 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 204 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1043 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 204 .northEast = true) : bonus 229 p ≤ bonus 204 p := by
  have certified := compare103 p (guard1043 p guard)
  simpa only [at229, at204, Int.zero_add] using certified
theorem check1043 (p : Pattern) : (!walkGuard soko3_2.board support p 229 204 .northEast || decide (bonus 229 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound1043 p)
theorem guard1044 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 202 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1044 (p : Pattern) (guard : walkGuard soko3_2.board support p 229 202 .northWest = true) : bonus 229 p ≤ bonus 202 p := by
  have certified := compare103 p (guard1044 p guard)
  simpa only [at229, at202, Int.zero_add] using certified
theorem check1044 (p : Pattern) : (!walkGuard soko3_2.board support p 229 202 .northWest || decide (bonus 229 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound1044 p)
theorem guard1045 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 204 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1045 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 204 .north = true) : bonus 230 p ≤ bonus 204 p := by
  have certified := compare103 p (guard1045 p guard)
  simpa only [at230, at204, Int.zero_add] using certified
theorem check1045 (p : Pattern) : (!walkGuard soko3_2.board support p 230 204 .north || decide (bonus 230 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound1045 p)
theorem guard1046 (p : Pattern) (guard : pushGuard support p 230 204 178 178 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1046 (p : Pattern) (guard : pushGuard support p 230 204 178 178 = true) : bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some 178)) := by
  have certified := compare37 p (guard1046 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 204 (some 178))
  have normalized := agree0 _ _ (change_representative support p 204 (some 178) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1046 (p : Pattern) : (!pushGuard support p 230 204 178 178 || decide (bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some 178)))) = true :=
  check_of_implication _ _ (bound1046 p)
theorem guard1047 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 231 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1047 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 231 .east = true) : bonus 230 p ≤ bonus 231 p := by
  have certified := compare103 p (guard1047 p guard)
  simpa only [at230, at231, Int.zero_add] using certified
theorem check1047 (p : Pattern) : (!walkGuard soko3_2.board support p 230 231 .east || decide (bonus 230 p ≤ bonus 231 p)) = true :=
  check_of_implication _ _ (bound1047 p)
theorem guard1048 (p : Pattern) (guard : pushGuard support p 230 231 232 232 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1048 (p : Pattern) (guard : pushGuard support p 230 231 232 232 = true) : bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder 232 - Generated.soko3_2Potential.boulder 231 + bonus 231 (change p 231 (some 232)) := by
  have certified := compare37 p (guard1048 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 231 (some 232))
  have normalized := agree0 _ _ (change_representative support p 231 (some 232) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1048 (p : Pattern) : (!pushGuard support p 230 231 232 232 || decide (bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder 232 - Generated.soko3_2Potential.boulder 231 + bonus 231 (change p 231 (some 232)))) = true :=
  check_of_implication _ _ (bound1048 p)
theorem guard1049 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 229 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1049 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 229 .west = true) : bonus 230 p ≤ bonus 229 p := by
  have certified := compare103 p (guard1049 p guard)
  simpa only [at230, at229, Int.zero_add] using certified
theorem check1049 (p : Pattern) : (!walkGuard soko3_2.board support p 230 229 .west || decide (bonus 230 p ≤ bonus 229 p)) = true :=
  check_of_implication _ _ (bound1049 p)
theorem guard1050 (p : Pattern) (guard : pushGuard support p 230 229 228 228 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1050 (p : Pattern) (guard : pushGuard support p 230 229 228 228 = true) : bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder 228 - Generated.soko3_2Potential.boulder 229 + bonus 229 (change p 229 (some 228)) := by
  have certified := compare37 p (guard1050 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 229 (some 228))
  have normalized := agree0 _ _ (change_representative support p 229 (some 228) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1050 (p : Pattern) : (!pushGuard support p 230 229 228 228 || decide (bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder 228 - Generated.soko3_2Potential.boulder 229 + bonus 229 (change p 229 (some 228)))) = true :=
  check_of_implication _ _ (bound1050 p)
theorem guard1051 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 205 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1051 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 205 .northEast = true) : bonus 230 p ≤ bonus 205 p := by
  have certified := compare103 p (guard1051 p guard)
  simpa only [at230, at205, Int.zero_add] using certified
theorem check1051 (p : Pattern) : (!walkGuard soko3_2.board support p 230 205 .northEast || decide (bonus 230 p ≤ bonus 205 p)) = true :=
  check_of_implication _ _ (bound1051 p)
theorem guard1052 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 203 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1052 (p : Pattern) (guard : walkGuard soko3_2.board support p 230 203 .northWest = true) : bonus 230 p ≤ bonus 203 p := by
  have certified := compare103 p (guard1052 p guard)
  simpa only [at230, at203, Int.zero_add] using certified
theorem check1052 (p : Pattern) : (!walkGuard soko3_2.board support p 230 203 .northWest || decide (bonus 230 p ≤ bonus 203 p)) = true :=
  check_of_implication _ _ (bound1052 p)
theorem guard1053 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 205 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1053 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 205 .north = true) : bonus 231 p ≤ bonus 205 p := by
  have certified := compare103 p (guard1053 p guard)
  simpa only [at231, at205, Int.zero_add] using certified
theorem check1053 (p : Pattern) : (!walkGuard soko3_2.board support p 231 205 .north || decide (bonus 231 p ≤ bonus 205 p)) = true :=
  check_of_implication _ _ (bound1053 p)
theorem guard1054 (p : Pattern) (guard : pushGuard support p 231 205 179 179 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1054 (p : Pattern) (guard : pushGuard support p 231 205 179 179 = true) : bonus 231 p ≤ 1 + Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some 179)) := by
  have certified := compare37 p (guard1054 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 205 (some 179))
  have normalized := agree0 _ _ (change_representative support p 205 (some 179) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1054 (p : Pattern) : (!pushGuard support p 231 205 179 179 || decide (bonus 231 p ≤ 1 + Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some 179)))) = true :=
  check_of_implication _ _ (bound1054 p)
theorem guard1055 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 232 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1055 (p : Pattern) (guard : walkGuard soko3_2.board support p 231 232 .east = true) : bonus 231 p ≤ bonus 232 p := by
  have certified := compare103 p (guard1055 p guard)
  simpa only [at231, at232, Int.zero_add] using certified
theorem check1055 (p : Pattern) : (!walkGuard soko3_2.board support p 231 232 .east || decide (bonus 231 p ≤ bonus 232 p)) = true :=
  check_of_implication _ _ (bound1055 p)
end NetHack.Sokoban32Refined
