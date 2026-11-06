import NetHack.Sokoban22Refined85.ActionBounds041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1008 (p : Pattern) (guard : pushGuard support p 252 253 254 254 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1008 (p : Pattern) (guard : pushGuard support p 252 253 254 254 = true) : bonus 252 p ≤ 1 - Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.hole 254 + bonus 253 (change p 253 none) := by
  have certified := compare33243 p (guard1008 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 253 none)
  have normalized := agree3224 _ _ (change_representative support p 253 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1008 (p : Pattern) : (!pushGuard support p 252 253 254 254 || decide (bonus 252 p ≤ 1 - Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.hole 254 + bonus 253 (change p 253 none))) = true :=
  check_of_implication _ _ (bound1008 p)
theorem guard1009 (p : Pattern) (guard : walkGuard soko2_2.board support p 252 251 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1009 (p : Pattern) (guard : walkGuard soko2_2.board support p 252 251 .west = true) : bonus 252 p ≤ bonus 251 p := by
  have certified := compare24907 p (guard1009 p guard)
  simpa only [at252, at251, Int.zero_add] using certified
theorem check1009 (p : Pattern) : (!walkGuard soko2_2.board support p 252 251 .west || decide (bonus 252 p ≤ bonus 251 p)) = true :=
  check_of_implication _ _ (bound1009 p)
theorem guard1010 (p : Pattern) (guard : pushGuard support p 252 251 250 250 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1010 (p : Pattern) (guard : pushGuard support p 252 251 250 250 = true) : bonus 252 p ≤ 1 + Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.boulder 251 + bonus 251 (change p 251 (some 250)) := by
  have certified := compare33243 p (guard1010 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 251 (some 250))
  have normalized := agree3224 _ _ (change_representative support p 251 (some 250) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1010 (p : Pattern) : (!pushGuard support p 252 251 250 250 || decide (bonus 252 p ≤ 1 + Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.boulder 251 + bonus 251 (change p 251 (some 250)))) = true :=
  check_of_implication _ _ (bound1010 p)
theorem guard1011 (p : Pattern) (guard : pushGuard support p 252 251 250 250 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1011 (p : Pattern) (guard : pushGuard support p 252 251 250 250 = true) : bonus 252 p ≤ 1 - Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.hole 250 + bonus 251 (change p 251 none) := by
  have certified := compare33243 p (guard1011 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 251 none)
  have normalized := agree3224 _ _ (change_representative support p 251 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1011 (p : Pattern) : (!pushGuard support p 252 251 250 250 || decide (bonus 252 p ≤ 1 - Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.hole 250 + bonus 251 (change p 251 none))) = true :=
  check_of_implication _ _ (bound1011 p)
theorem guard1012 (p : Pattern) (guard : walkGuard soko2_2.board support p 253 254 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1012 (p : Pattern) (guard : walkGuard soko2_2.board support p 253 254 .east = true) : bonus 253 p ≤ bonus 254 p := by
  have certified := compare24907 p (guard1012 p guard)
  simpa only [at253, at254, Int.zero_add] using certified
theorem check1012 (p : Pattern) : (!walkGuard soko2_2.board support p 253 254 .east || decide (bonus 253 p ≤ bonus 254 p)) = true :=
  check_of_implication _ _ (bound1012 p)
theorem guard1013 (p : Pattern) (guard : pushGuard support p 253 254 255 255 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1013 (p : Pattern) (guard : pushGuard support p 253 254 255 255 = true) : bonus 253 p ≤ 1 + Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.boulder 254 + bonus 254 (change p 254 (some 255)) := by
  have certified := compare33243 p (guard1013 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 254 (some 255))
  have normalized := agree3224 _ _ (change_representative support p 254 (some 255) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1013 (p : Pattern) : (!pushGuard support p 253 254 255 255 || decide (bonus 253 p ≤ 1 + Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.boulder 254 + bonus 254 (change p 254 (some 255)))) = true :=
  check_of_implication _ _ (bound1013 p)
theorem guard1014 (p : Pattern) (guard : pushGuard support p 253 254 255 255 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1014 (p : Pattern) (guard : pushGuard support p 253 254 255 255 = true) : bonus 253 p ≤ 1 - Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.hole 255 + bonus 254 (change p 254 none) := by
  have certified := compare33243 p (guard1014 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 254 none)
  have normalized := agree3224 _ _ (change_representative support p 254 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1014 (p : Pattern) : (!pushGuard support p 253 254 255 255 || decide (bonus 253 p ≤ 1 - Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.hole 255 + bonus 254 (change p 254 none))) = true :=
  check_of_implication _ _ (bound1014 p)
theorem guard1015 (p : Pattern) (guard : walkGuard soko2_2.board support p 253 252 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1015 (p : Pattern) (guard : walkGuard soko2_2.board support p 253 252 .west = true) : bonus 253 p ≤ bonus 252 p := by
  have certified := compare24907 p (guard1015 p guard)
  simpa only [at253, at252, Int.zero_add] using certified
theorem check1015 (p : Pattern) : (!walkGuard soko2_2.board support p 253 252 .west || decide (bonus 253 p ≤ bonus 252 p)) = true :=
  check_of_implication _ _ (bound1015 p)
theorem guard1016 (p : Pattern) (guard : pushGuard support p 253 252 251 251 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1016 (p : Pattern) (guard : pushGuard support p 253 252 251 251 = true) : bonus 253 p ≤ 1 + Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.boulder 252 + bonus 252 (change p 252 (some 251)) := by
  have certified := compare33243 p (guard1016 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 252 (some 251))
  have normalized := agree3224 _ _ (change_representative support p 252 (some 251) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1016 (p : Pattern) : (!pushGuard support p 253 252 251 251 || decide (bonus 253 p ≤ 1 + Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.boulder 252 + bonus 252 (change p 252 (some 251)))) = true :=
  check_of_implication _ _ (bound1016 p)
theorem guard1017 (p : Pattern) (guard : pushGuard support p 253 252 251 251 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1017 (p : Pattern) (guard : pushGuard support p 253 252 251 251 = true) : bonus 253 p ≤ 1 - Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.hole 251 + bonus 252 (change p 252 none) := by
  have certified := compare33243 p (guard1017 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 252 none)
  have normalized := agree3224 _ _ (change_representative support p 252 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1017 (p : Pattern) : (!pushGuard support p 253 252 251 251 || decide (bonus 253 p ≤ 1 - Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.hole 251 + bonus 252 (change p 252 none))) = true :=
  check_of_implication _ _ (bound1017 p)
theorem guard1018 (p : Pattern) (guard : walkGuard soko2_2.board support p 254 255 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1018 (p : Pattern) (guard : walkGuard soko2_2.board support p 254 255 .east = true) : bonus 254 p ≤ bonus 255 p := by
  have certified := compare24907 p (guard1018 p guard)
  simpa only [at254, at255, Int.zero_add] using certified
theorem check1018 (p : Pattern) : (!walkGuard soko2_2.board support p 254 255 .east || decide (bonus 254 p ≤ bonus 255 p)) = true :=
  check_of_implication _ _ (bound1018 p)
theorem guard1019 (p : Pattern) (guard : pushGuard support p 254 255 256 256 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1019 (p : Pattern) (guard : pushGuard support p 254 255 256 256 = true) : bonus 254 p ≤ 1 + Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.boulder 255 + bonus 255 (change p 255 (some 256)) := by
  have certified := compare33243 p (guard1019 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 255 (some 256))
  have normalized := agree3224 _ _ (change_representative support p 255 (some 256) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1019 (p : Pattern) : (!pushGuard support p 254 255 256 256 || decide (bonus 254 p ≤ 1 + Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.boulder 255 + bonus 255 (change p 255 (some 256)))) = true :=
  check_of_implication _ _ (bound1019 p)
theorem guard1020 (p : Pattern) (guard : pushGuard support p 254 255 256 256 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1020 (p : Pattern) (guard : pushGuard support p 254 255 256 256 = true) : bonus 254 p ≤ 1 - Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.hole 256 + bonus 255 (change p 255 none) := by
  have certified := compare33243 p (guard1020 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 255 none)
  have normalized := agree3224 _ _ (change_representative support p 255 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1020 (p : Pattern) : (!pushGuard support p 254 255 256 256 || decide (bonus 254 p ≤ 1 - Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.hole 256 + bonus 255 (change p 255 none))) = true :=
  check_of_implication _ _ (bound1020 p)
theorem guard1021 (p : Pattern) (guard : walkGuard soko2_2.board support p 254 253 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1021 (p : Pattern) (guard : walkGuard soko2_2.board support p 254 253 .west = true) : bonus 254 p ≤ bonus 253 p := by
  have certified := compare24907 p (guard1021 p guard)
  simpa only [at254, at253, Int.zero_add] using certified
theorem check1021 (p : Pattern) : (!walkGuard soko2_2.board support p 254 253 .west || decide (bonus 254 p ≤ bonus 253 p)) = true :=
  check_of_implication _ _ (bound1021 p)
theorem guard1022 (p : Pattern) (guard : pushGuard support p 254 253 252 252 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1022 (p : Pattern) (guard : pushGuard support p 254 253 252 252 = true) : bonus 254 p ≤ 1 + Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.boulder 253 + bonus 253 (change p 253 (some 252)) := by
  have certified := compare33243 p (guard1022 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 253 (some 252))
  have normalized := agree3224 _ _ (change_representative support p 253 (some 252) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1022 (p : Pattern) : (!pushGuard support p 254 253 252 252 || decide (bonus 254 p ≤ 1 + Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.boulder 253 + bonus 253 (change p 253 (some 252)))) = true :=
  check_of_implication _ _ (bound1022 p)
theorem guard1023 (p : Pattern) (guard : pushGuard support p 254 253 252 252 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1023 (p : Pattern) (guard : pushGuard support p 254 253 252 252 = true) : bonus 254 p ≤ 1 - Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.hole 252 + bonus 253 (change p 253 none) := by
  have certified := compare33243 p (guard1023 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 253 none)
  have normalized := agree3224 _ _ (change_representative support p 253 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1023 (p : Pattern) : (!pushGuard support p 254 253 252 252 || decide (bonus 254 p ≤ 1 - Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.hole 252 + bonus 253 (change p 253 none))) = true :=
  check_of_implication _ _ (bound1023 p)
theorem guard1024 (p : Pattern) (guard : walkGuard soko2_2.board support p 255 256 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1024 (p : Pattern) (guard : walkGuard soko2_2.board support p 255 256 .east = true) : bonus 255 p ≤ bonus 256 p := by
  have certified := compare24907 p (guard1024 p guard)
  simpa only [at255, at256, Int.zero_add] using certified
theorem check1024 (p : Pattern) : (!walkGuard soko2_2.board support p 255 256 .east || decide (bonus 255 p ≤ bonus 256 p)) = true :=
  check_of_implication _ _ (bound1024 p)
theorem guard1025 (p : Pattern) (guard : pushGuard support p 255 256 257 257 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1025 (p : Pattern) (guard : pushGuard support p 255 256 257 257 = true) : bonus 255 p ≤ 1 + Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.boulder 256 + bonus 256 (change p 256 (some 257)) := by
  have certified := compare33243 p (guard1025 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 256 (some 257))
  have normalized := agree3224 _ _ (change_representative support p 256 (some 257) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1025 (p : Pattern) : (!pushGuard support p 255 256 257 257 || decide (bonus 255 p ≤ 1 + Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.boulder 256 + bonus 256 (change p 256 (some 257)))) = true :=
  check_of_implication _ _ (bound1025 p)
theorem guard1026 (p : Pattern) (guard : pushGuard support p 255 256 257 257 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1026 (p : Pattern) (guard : pushGuard support p 255 256 257 257 = true) : bonus 255 p ≤ 1 - Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.hole 257 + bonus 256 (change p 256 none) := by
  have certified := compare33243 p (guard1026 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 256 none)
  have normalized := agree3224 _ _ (change_representative support p 256 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1026 (p : Pattern) : (!pushGuard support p 255 256 257 257 || decide (bonus 255 p ≤ 1 - Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.hole 257 + bonus 256 (change p 256 none))) = true :=
  check_of_implication _ _ (bound1026 p)
theorem guard1027 (p : Pattern) (guard : walkGuard soko2_2.board support p 255 254 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1027 (p : Pattern) (guard : walkGuard soko2_2.board support p 255 254 .west = true) : bonus 255 p ≤ bonus 254 p := by
  have certified := compare24907 p (guard1027 p guard)
  simpa only [at255, at254, Int.zero_add] using certified
theorem check1027 (p : Pattern) : (!walkGuard soko2_2.board support p 255 254 .west || decide (bonus 255 p ≤ bonus 254 p)) = true :=
  check_of_implication _ _ (bound1027 p)
theorem guard1028 (p : Pattern) (guard : pushGuard support p 255 254 253 253 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1028 (p : Pattern) (guard : pushGuard support p 255 254 253 253 = true) : bonus 255 p ≤ 1 + Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.boulder 254 + bonus 254 (change p 254 (some 253)) := by
  have certified := compare33243 p (guard1028 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 254 (some 253))
  have normalized := agree3224 _ _ (change_representative support p 254 (some 253) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1028 (p : Pattern) : (!pushGuard support p 255 254 253 253 || decide (bonus 255 p ≤ 1 + Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.boulder 254 + bonus 254 (change p 254 (some 253)))) = true :=
  check_of_implication _ _ (bound1028 p)
theorem guard1029 (p : Pattern) (guard : pushGuard support p 255 254 253 253 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1029 (p : Pattern) (guard : pushGuard support p 255 254 253 253 = true) : bonus 255 p ≤ 1 - Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.hole 253 + bonus 254 (change p 254 none) := by
  have certified := compare33243 p (guard1029 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 254 none)
  have normalized := agree3224 _ _ (change_representative support p 254 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1029 (p : Pattern) : (!pushGuard support p 255 254 253 253 || decide (bonus 255 p ≤ 1 - Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.hole 253 + bonus 254 (change p 254 none))) = true :=
  check_of_implication _ _ (bound1029 p)
theorem guard1030 (p : Pattern) (guard : walkGuard soko2_2.board support p 256 257 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1030 (p : Pattern) (guard : walkGuard soko2_2.board support p 256 257 .east = true) : bonus 256 p ≤ bonus 257 p := by
  have certified := compare24907 p (guard1030 p guard)
  simpa only [at256, at257, Int.zero_add] using certified
theorem check1030 (p : Pattern) : (!walkGuard soko2_2.board support p 256 257 .east || decide (bonus 256 p ≤ bonus 257 p)) = true :=
  check_of_implication _ _ (bound1030 p)
theorem guard1031 (p : Pattern) (guard : pushGuard support p 256 257 258 258 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1031 (p : Pattern) (guard : pushGuard support p 256 257 258 258 = true) : bonus 256 p ≤ 1 + Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.boulder 257 + bonus 257 (change p 257 (some 258)) := by
  have certified := compare33243 p (guard1031 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 257 (some 258))
  have normalized := agree3224 _ _ (change_representative support p 257 (some 258) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1031 (p : Pattern) : (!pushGuard support p 256 257 258 258 || decide (bonus 256 p ≤ 1 + Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.boulder 257 + bonus 257 (change p 257 (some 258)))) = true :=
  check_of_implication _ _ (bound1031 p)
end NetHack.Sokoban22Refined85
