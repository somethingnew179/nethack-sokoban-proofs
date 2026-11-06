import NetHack.Sokoban22Refined85.ActionBounds042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1032 (p : Pattern) (guard : pushGuard support p 256 257 258 258 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1032 (p : Pattern) (guard : pushGuard support p 256 257 258 258 = true) : bonus 256 p ≤ 1 - Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.hole 258 + bonus 257 (change p 257 none) := by
  have certified := compare33243 p (guard1032 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 257 none)
  have normalized := agree3224 _ _ (change_representative support p 257 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1032 (p : Pattern) : (!pushGuard support p 256 257 258 258 || decide (bonus 256 p ≤ 1 - Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.hole 258 + bonus 257 (change p 257 none))) = true :=
  check_of_implication _ _ (bound1032 p)
theorem guard1033 (p : Pattern) (guard : walkGuard soko2_2.board support p 256 255 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1033 (p : Pattern) (guard : walkGuard soko2_2.board support p 256 255 .west = true) : bonus 256 p ≤ bonus 255 p := by
  have certified := compare24907 p (guard1033 p guard)
  simpa only [at256, at255, Int.zero_add] using certified
theorem check1033 (p : Pattern) : (!walkGuard soko2_2.board support p 256 255 .west || decide (bonus 256 p ≤ bonus 255 p)) = true :=
  check_of_implication _ _ (bound1033 p)
theorem guard1034 (p : Pattern) (guard : pushGuard support p 256 255 254 254 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1034 (p : Pattern) (guard : pushGuard support p 256 255 254 254 = true) : bonus 256 p ≤ 1 + Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.boulder 255 + bonus 255 (change p 255 (some 254)) := by
  have certified := compare33243 p (guard1034 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 255 (some 254))
  have normalized := agree3224 _ _ (change_representative support p 255 (some 254) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1034 (p : Pattern) : (!pushGuard support p 256 255 254 254 || decide (bonus 256 p ≤ 1 + Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.boulder 255 + bonus 255 (change p 255 (some 254)))) = true :=
  check_of_implication _ _ (bound1034 p)
theorem guard1035 (p : Pattern) (guard : pushGuard support p 256 255 254 254 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1035 (p : Pattern) (guard : pushGuard support p 256 255 254 254 = true) : bonus 256 p ≤ 1 - Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.hole 254 + bonus 255 (change p 255 none) := by
  have certified := compare33243 p (guard1035 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 255 none)
  have normalized := agree3224 _ _ (change_representative support p 255 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1035 (p : Pattern) : (!pushGuard support p 256 255 254 254 || decide (bonus 256 p ≤ 1 - Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.hole 254 + bonus 255 (change p 255 none))) = true :=
  check_of_implication _ _ (bound1035 p)
theorem guard1036 (p : Pattern) (guard : walkGuard soko2_2.board support p 257 258 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1036 (p : Pattern) (guard : walkGuard soko2_2.board support p 257 258 .east = true) : bonus 257 p ≤ bonus 258 p := by
  have certified := compare24907 p (guard1036 p guard)
  simpa only [at257, at258, Int.zero_add] using certified
theorem check1036 (p : Pattern) : (!walkGuard soko2_2.board support p 257 258 .east || decide (bonus 257 p ≤ bonus 258 p)) = true :=
  check_of_implication _ _ (bound1036 p)
theorem guard1037 (p : Pattern) (guard : pushGuard support p 257 258 259 259 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1037 (p : Pattern) (guard : pushGuard support p 257 258 259 259 = true) : bonus 257 p ≤ 1 + Generated.soko2_2Potential.boulder 259 - Generated.soko2_2Potential.boulder 258 + bonus 258 (change p 258 (some 259)) := by
  have certified := compare33243 p (guard1037 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 258 (some 259))
  have normalized := agree3224 _ _ (change_representative support p 258 (some 259) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1037 (p : Pattern) : (!pushGuard support p 257 258 259 259 || decide (bonus 257 p ≤ 1 + Generated.soko2_2Potential.boulder 259 - Generated.soko2_2Potential.boulder 258 + bonus 258 (change p 258 (some 259)))) = true :=
  check_of_implication _ _ (bound1037 p)
theorem guard1038 (p : Pattern) (guard : pushGuard support p 257 258 259 259 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1038 (p : Pattern) (guard : pushGuard support p 257 258 259 259 = true) : bonus 257 p ≤ 1 - Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.hole 259 + bonus 258 (change p 258 none) := by
  have certified := compare33243 p (guard1038 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 258 none)
  have normalized := agree3224 _ _ (change_representative support p 258 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1038 (p : Pattern) : (!pushGuard support p 257 258 259 259 || decide (bonus 257 p ≤ 1 - Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.hole 259 + bonus 258 (change p 258 none))) = true :=
  check_of_implication _ _ (bound1038 p)
theorem guard1039 (p : Pattern) (guard : walkGuard soko2_2.board support p 257 256 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1039 (p : Pattern) (guard : walkGuard soko2_2.board support p 257 256 .west = true) : bonus 257 p ≤ bonus 256 p := by
  have certified := compare24907 p (guard1039 p guard)
  simpa only [at257, at256, Int.zero_add] using certified
theorem check1039 (p : Pattern) : (!walkGuard soko2_2.board support p 257 256 .west || decide (bonus 257 p ≤ bonus 256 p)) = true :=
  check_of_implication _ _ (bound1039 p)
theorem guard1040 (p : Pattern) (guard : pushGuard support p 257 256 255 255 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1040 (p : Pattern) (guard : pushGuard support p 257 256 255 255 = true) : bonus 257 p ≤ 1 + Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.boulder 256 + bonus 256 (change p 256 (some 255)) := by
  have certified := compare33243 p (guard1040 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 256 (some 255))
  have normalized := agree3224 _ _ (change_representative support p 256 (some 255) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1040 (p : Pattern) : (!pushGuard support p 257 256 255 255 || decide (bonus 257 p ≤ 1 + Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.boulder 256 + bonus 256 (change p 256 (some 255)))) = true :=
  check_of_implication _ _ (bound1040 p)
theorem guard1041 (p : Pattern) (guard : pushGuard support p 257 256 255 255 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1041 (p : Pattern) (guard : pushGuard support p 257 256 255 255 = true) : bonus 257 p ≤ 1 - Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.hole 255 + bonus 256 (change p 256 none) := by
  have certified := compare33243 p (guard1041 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 256 none)
  have normalized := agree3224 _ _ (change_representative support p 256 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1041 (p : Pattern) : (!pushGuard support p 257 256 255 255 || decide (bonus 257 p ≤ 1 - Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.hole 255 + bonus 256 (change p 256 none))) = true :=
  check_of_implication _ _ (bound1041 p)
theorem guard1042 (p : Pattern) (guard : walkGuard soko2_2.board support p 258 259 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1042 (p : Pattern) (guard : walkGuard soko2_2.board support p 258 259 .east = true) : bonus 258 p ≤ bonus 259 p := by
  have certified := compare24907 p (guard1042 p guard)
  simpa only [at258, at259, Int.zero_add] using certified
theorem check1042 (p : Pattern) : (!walkGuard soko2_2.board support p 258 259 .east || decide (bonus 258 p ≤ bonus 259 p)) = true :=
  check_of_implication _ _ (bound1042 p)
theorem guard1043 (p : Pattern) (guard : pushGuard support p 258 259 260 260 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1043 (p : Pattern) (guard : pushGuard support p 258 259 260 260 = true) : bonus 258 p ≤ 1 + Generated.soko2_2Potential.boulder 260 - Generated.soko2_2Potential.boulder 259 + bonus 259 (change p 259 (some 260)) := by
  have certified := compare33243 p (guard1043 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 259 (some 260))
  have normalized := agree3224 _ _ (change_representative support p 259 (some 260) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1043 (p : Pattern) : (!pushGuard support p 258 259 260 260 || decide (bonus 258 p ≤ 1 + Generated.soko2_2Potential.boulder 260 - Generated.soko2_2Potential.boulder 259 + bonus 259 (change p 259 (some 260)))) = true :=
  check_of_implication _ _ (bound1043 p)
theorem guard1044 (p : Pattern) (guard : pushGuard support p 258 259 260 260 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1044 (p : Pattern) (guard : pushGuard support p 258 259 260 260 = true) : bonus 258 p ≤ 1 - Generated.soko2_2Potential.boulder 259 - Generated.soko2_2Potential.hole 260 + bonus 259 (change p 259 none) := by
  have certified := compare33243 p (guard1044 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 259 none)
  have normalized := agree3224 _ _ (change_representative support p 259 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1044 (p : Pattern) : (!pushGuard support p 258 259 260 260 || decide (bonus 258 p ≤ 1 - Generated.soko2_2Potential.boulder 259 - Generated.soko2_2Potential.hole 260 + bonus 259 (change p 259 none))) = true :=
  check_of_implication _ _ (bound1044 p)
theorem guard1045 (p : Pattern) (guard : walkGuard soko2_2.board support p 258 257 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1045 (p : Pattern) (guard : walkGuard soko2_2.board support p 258 257 .west = true) : bonus 258 p ≤ bonus 257 p := by
  have certified := compare24907 p (guard1045 p guard)
  simpa only [at258, at257, Int.zero_add] using certified
theorem check1045 (p : Pattern) : (!walkGuard soko2_2.board support p 258 257 .west || decide (bonus 258 p ≤ bonus 257 p)) = true :=
  check_of_implication _ _ (bound1045 p)
theorem guard1046 (p : Pattern) (guard : pushGuard support p 258 257 256 256 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1046 (p : Pattern) (guard : pushGuard support p 258 257 256 256 = true) : bonus 258 p ≤ 1 + Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.boulder 257 + bonus 257 (change p 257 (some 256)) := by
  have certified := compare33243 p (guard1046 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 257 (some 256))
  have normalized := agree3224 _ _ (change_representative support p 257 (some 256) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1046 (p : Pattern) : (!pushGuard support p 258 257 256 256 || decide (bonus 258 p ≤ 1 + Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.boulder 257 + bonus 257 (change p 257 (some 256)))) = true :=
  check_of_implication _ _ (bound1046 p)
theorem guard1047 (p : Pattern) (guard : pushGuard support p 258 257 256 256 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1047 (p : Pattern) (guard : pushGuard support p 258 257 256 256 = true) : bonus 258 p ≤ 1 - Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.hole 256 + bonus 257 (change p 257 none) := by
  have certified := compare33243 p (guard1047 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 257 none)
  have normalized := agree3224 _ _ (change_representative support p 257 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1047 (p : Pattern) : (!pushGuard support p 258 257 256 256 || decide (bonus 258 p ≤ 1 - Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.hole 256 + bonus 257 (change p 257 none))) = true :=
  check_of_implication _ _ (bound1047 p)
theorem guard1048 (p : Pattern) (guard : walkGuard soko2_2.board support p 259 260 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1048 (p : Pattern) (guard : walkGuard soko2_2.board support p 259 260 .east = true) : bonus 259 p ≤ bonus 260 p := by
  have certified := compare24907 p (guard1048 p guard)
  simpa only [at259, at260, Int.zero_add] using certified
theorem check1048 (p : Pattern) : (!walkGuard soko2_2.board support p 259 260 .east || decide (bonus 259 p ≤ bonus 260 p)) = true :=
  check_of_implication _ _ (bound1048 p)
theorem guard1049 (p : Pattern) (guard : walkGuard soko2_2.board support p 259 258 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1049 (p : Pattern) (guard : walkGuard soko2_2.board support p 259 258 .west = true) : bonus 259 p ≤ bonus 258 p := by
  have certified := compare24907 p (guard1049 p guard)
  simpa only [at259, at258, Int.zero_add] using certified
theorem check1049 (p : Pattern) : (!walkGuard soko2_2.board support p 259 258 .west || decide (bonus 259 p ≤ bonus 258 p)) = true :=
  check_of_implication _ _ (bound1049 p)
theorem guard1050 (p : Pattern) (guard : pushGuard support p 259 258 257 257 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1050 (p : Pattern) (guard : pushGuard support p 259 258 257 257 = true) : bonus 259 p ≤ 1 + Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.boulder 258 + bonus 258 (change p 258 (some 257)) := by
  have certified := compare33243 p (guard1050 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 258 (some 257))
  have normalized := agree3224 _ _ (change_representative support p 258 (some 257) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1050 (p : Pattern) : (!pushGuard support p 259 258 257 257 || decide (bonus 259 p ≤ 1 + Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.boulder 258 + bonus 258 (change p 258 (some 257)))) = true :=
  check_of_implication _ _ (bound1050 p)
theorem guard1051 (p : Pattern) (guard : pushGuard support p 259 258 257 257 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1051 (p : Pattern) (guard : pushGuard support p 259 258 257 257 = true) : bonus 259 p ≤ 1 - Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.hole 257 + bonus 258 (change p 258 none) := by
  have certified := compare33243 p (guard1051 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 258 none)
  have normalized := agree3224 _ _ (change_representative support p 258 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1051 (p : Pattern) : (!pushGuard support p 259 258 257 257 || decide (bonus 259 p ≤ 1 - Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.hole 257 + bonus 258 (change p 258 none))) = true :=
  check_of_implication _ _ (bound1051 p)
theorem guard1052 (p : Pattern) (guard : walkGuard soko2_2.board support p 260 259 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1052 (p : Pattern) (guard : walkGuard soko2_2.board support p 260 259 .west = true) : bonus 260 p ≤ bonus 259 p := by
  have certified := compare24907 p (guard1052 p guard)
  simpa only [at260, at259, Int.zero_add] using certified
theorem check1052 (p : Pattern) : (!walkGuard soko2_2.board support p 260 259 .west || decide (bonus 260 p ≤ bonus 259 p)) = true :=
  check_of_implication _ _ (bound1052 p)
theorem guard1053 (p : Pattern) (guard : pushGuard support p 260 259 258 258 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1053 (p : Pattern) (guard : pushGuard support p 260 259 258 258 = true) : bonus 260 p ≤ 1 + Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.boulder 259 + bonus 259 (change p 259 (some 258)) := by
  have certified := compare33243 p (guard1053 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 259 (some 258))
  have normalized := agree3224 _ _ (change_representative support p 259 (some 258) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1053 (p : Pattern) : (!pushGuard support p 260 259 258 258 || decide (bonus 260 p ≤ 1 + Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.boulder 259 + bonus 259 (change p 259 (some 258)))) = true :=
  check_of_implication _ _ (bound1053 p)
theorem guard1054 (p : Pattern) (guard : pushGuard support p 260 259 258 258 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1054 (p : Pattern) (guard : pushGuard support p 260 259 258 258 = true) : bonus 260 p ≤ 1 - Generated.soko2_2Potential.boulder 259 - Generated.soko2_2Potential.hole 258 + bonus 259 (change p 259 none) := by
  have certified := compare33243 p (guard1054 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 259 none)
  have normalized := agree3224 _ _ (change_representative support p 259 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1054 (p : Pattern) : (!pushGuard support p 260 259 258 258 || decide (bonus 260 p ≤ 1 - Generated.soko2_2Potential.boulder 259 - Generated.soko2_2Potential.hole 258 + bonus 259 (change p 259 none))) = true :=
  check_of_implication _ _ (bound1054 p)
theorem guard1055 (p : Pattern) (guard : walkGuard soko2_2.board support p 262 240 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1055 (p : Pattern) (guard : walkGuard soko2_2.board support p 262 240 .north = true) : bonus 262 p ≤ bonus 240 p := by
  have certified := compare1086 p (guard1055 p guard)
  simpa only [at262, at240, Int.zero_add] using certified
theorem check1055 (p : Pattern) : (!walkGuard soko2_2.board support p 262 240 .north || decide (bonus 262 p ≤ bonus 240 p)) = true :=
  check_of_implication _ _ (bound1055 p)
end NetHack.Sokoban22Refined85
