import NetHack.Sokoban32Refined.ActionBounds041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1008 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 226 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1008 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 226 .east = true) : bonus 225 p ≤ bonus 226 p := by
  have certified := compare103 p (guard1008 p guard)
  simpa only [at225, at226, Int.zero_add] using certified
theorem check1008 (p : Pattern) : (!walkGuard soko3_2.board support p 225 226 .east || decide (bonus 225 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound1008 p)
theorem guard1009 (p : Pattern) (guard : pushGuard support p 225 226 227 227 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1009 (p : Pattern) (guard : pushGuard support p 225 226 227 227 = true) : bonus 225 p ≤ 1 + Generated.soko3_2Potential.boulder 227 - Generated.soko3_2Potential.boulder 226 + bonus 226 (change p 226 (some 227)) := by
  have certified := compare37 p (guard1009 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 226 (some 227))
  have normalized := agree0 _ _ (change_representative support p 226 (some 227) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1009 (p : Pattern) : (!pushGuard support p 225 226 227 227 || decide (bonus 225 p ≤ 1 + Generated.soko3_2Potential.boulder 227 - Generated.soko3_2Potential.boulder 226 + bonus 226 (change p 226 (some 227)))) = true :=
  check_of_implication _ _ (bound1009 p)
theorem guard1010 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 224 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1010 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 224 .west = true) : bonus 225 p ≤ bonus 224 p := by
  have certified := compare103 p (guard1010 p guard)
  simpa only [at225, at224, Int.zero_add] using certified
theorem check1010 (p : Pattern) : (!walkGuard soko3_2.board support p 225 224 .west || decide (bonus 225 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound1010 p)
theorem guard1011 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 200 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1011 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 200 .northEast = true) : bonus 225 p ≤ bonus 200 p := by
  have certified := compare103 p (guard1011 p guard)
  simpa only [at225, at200, Int.zero_add] using certified
theorem check1011 (p : Pattern) : (!walkGuard soko3_2.board support p 225 200 .northEast || decide (bonus 225 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound1011 p)
theorem guard1012 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 198 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1012 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 198 .northWest = true) : bonus 225 p ≤ bonus 198 p := by
  have certified := compare103 p (guard1012 p guard)
  simpa only [at225, at198, Int.zero_add] using certified
theorem check1012 (p : Pattern) : (!walkGuard soko3_2.board support p 225 198 .northWest || decide (bonus 225 p ≤ bonus 198 p)) = true :=
  check_of_implication _ _ (bound1012 p)
theorem guard1013 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 200 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1013 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 200 .north = true) : bonus 226 p ≤ bonus 200 p := by
  have certified := compare103 p (guard1013 p guard)
  simpa only [at226, at200, Int.zero_add] using certified
theorem check1013 (p : Pattern) : (!walkGuard soko3_2.board support p 226 200 .north || decide (bonus 226 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound1013 p)
theorem guard1014 (p : Pattern) (guard : pushGuard support p 226 200 174 174 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1014 (p : Pattern) (guard : pushGuard support p 226 200 174 174 = true) : bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some 174)) := by
  have certified := compare37 p (guard1014 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 200 (some 174))
  have normalized := agree0 _ _ (change_representative support p 200 (some 174) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1014 (p : Pattern) : (!pushGuard support p 226 200 174 174 || decide (bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some 174)))) = true :=
  check_of_implication _ _ (bound1014 p)
theorem guard1015 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 227 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1015 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 227 .east = true) : bonus 226 p ≤ bonus 227 p := by
  have certified := compare103 p (guard1015 p guard)
  simpa only [at226, at227, Int.zero_add] using certified
theorem check1015 (p : Pattern) : (!walkGuard soko3_2.board support p 226 227 .east || decide (bonus 226 p ≤ bonus 227 p)) = true :=
  check_of_implication _ _ (bound1015 p)
theorem guard1016 (p : Pattern) (guard : pushGuard support p 226 227 228 228 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1016 (p : Pattern) (guard : pushGuard support p 226 227 228 228 = true) : bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder 228 - Generated.soko3_2Potential.boulder 227 + bonus 227 (change p 227 (some 228)) := by
  have certified := compare37 p (guard1016 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 227 (some 228))
  have normalized := agree0 _ _ (change_representative support p 227 (some 228) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1016 (p : Pattern) : (!pushGuard support p 226 227 228 228 || decide (bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder 228 - Generated.soko3_2Potential.boulder 227 + bonus 227 (change p 227 (some 228)))) = true :=
  check_of_implication _ _ (bound1016 p)
theorem guard1017 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 225 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1017 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 225 .west = true) : bonus 226 p ≤ bonus 225 p := by
  have certified := compare103 p (guard1017 p guard)
  simpa only [at226, at225, Int.zero_add] using certified
theorem check1017 (p : Pattern) : (!walkGuard soko3_2.board support p 226 225 .west || decide (bonus 226 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound1017 p)
theorem guard1018 (p : Pattern) (guard : pushGuard support p 226 225 224 224 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1018 (p : Pattern) (guard : pushGuard support p 226 225 224 224 = true) : bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder 224 - Generated.soko3_2Potential.boulder 225 + bonus 225 (change p 225 (some 224)) := by
  have certified := compare37 p (guard1018 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 225 (some 224))
  have normalized := agree0 _ _ (change_representative support p 225 (some 224) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1018 (p : Pattern) : (!pushGuard support p 226 225 224 224 || decide (bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder 224 - Generated.soko3_2Potential.boulder 225 + bonus 225 (change p 225 (some 224)))) = true :=
  check_of_implication _ _ (bound1018 p)
theorem guard1019 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 201 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1019 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 201 .northEast = true) : bonus 226 p ≤ bonus 201 p := by
  have certified := compare103 p (guard1019 p guard)
  simpa only [at226, at201, Int.zero_add] using certified
theorem check1019 (p : Pattern) : (!walkGuard soko3_2.board support p 226 201 .northEast || decide (bonus 226 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound1019 p)
theorem guard1020 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 199 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1020 (p : Pattern) (guard : walkGuard soko3_2.board support p 226 199 .northWest = true) : bonus 226 p ≤ bonus 199 p := by
  have certified := compare103 p (guard1020 p guard)
  simpa only [at226, at199, Int.zero_add] using certified
theorem check1020 (p : Pattern) : (!walkGuard soko3_2.board support p 226 199 .northWest || decide (bonus 226 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound1020 p)
theorem guard1021 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 201 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1021 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 201 .north = true) : bonus 227 p ≤ bonus 201 p := by
  have certified := compare103 p (guard1021 p guard)
  simpa only [at227, at201, Int.zero_add] using certified
theorem check1021 (p : Pattern) : (!walkGuard soko3_2.board support p 227 201 .north || decide (bonus 227 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound1021 p)
theorem guard1022 (p : Pattern) (guard : pushGuard support p 227 201 175 175 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1022 (p : Pattern) (guard : pushGuard support p 227 201 175 175 = true) : bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some 175)) := by
  have certified := compare37 p (guard1022 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 201 (some 175))
  have normalized := agree0 _ _ (change_representative support p 201 (some 175) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1022 (p : Pattern) : (!pushGuard support p 227 201 175 175 || decide (bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some 175)))) = true :=
  check_of_implication _ _ (bound1022 p)
theorem guard1023 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 228 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1023 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 228 .east = true) : bonus 227 p ≤ bonus 228 p := by
  have certified := compare103 p (guard1023 p guard)
  simpa only [at227, at228, Int.zero_add] using certified
theorem check1023 (p : Pattern) : (!walkGuard soko3_2.board support p 227 228 .east || decide (bonus 227 p ≤ bonus 228 p)) = true :=
  check_of_implication _ _ (bound1023 p)
theorem guard1024 (p : Pattern) (guard : pushGuard support p 227 228 229 229 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1024 (p : Pattern) (guard : pushGuard support p 227 228 229 229 = true) : bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder 229 - Generated.soko3_2Potential.boulder 228 + bonus 228 (change p 228 (some 229)) := by
  have certified := compare37 p (guard1024 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 228 (some 229))
  have normalized := agree0 _ _ (change_representative support p 228 (some 229) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1024 (p : Pattern) : (!pushGuard support p 227 228 229 229 || decide (bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder 229 - Generated.soko3_2Potential.boulder 228 + bonus 228 (change p 228 (some 229)))) = true :=
  check_of_implication _ _ (bound1024 p)
theorem guard1025 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 226 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1025 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 226 .west = true) : bonus 227 p ≤ bonus 226 p := by
  have certified := compare103 p (guard1025 p guard)
  simpa only [at227, at226, Int.zero_add] using certified
theorem check1025 (p : Pattern) : (!walkGuard soko3_2.board support p 227 226 .west || decide (bonus 227 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound1025 p)
theorem guard1026 (p : Pattern) (guard : pushGuard support p 227 226 225 225 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1026 (p : Pattern) (guard : pushGuard support p 227 226 225 225 = true) : bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder 225 - Generated.soko3_2Potential.boulder 226 + bonus 226 (change p 226 (some 225)) := by
  have certified := compare37 p (guard1026 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 226 (some 225))
  have normalized := agree0 _ _ (change_representative support p 226 (some 225) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1026 (p : Pattern) : (!pushGuard support p 227 226 225 225 || decide (bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder 225 - Generated.soko3_2Potential.boulder 226 + bonus 226 (change p 226 (some 225)))) = true :=
  check_of_implication _ _ (bound1026 p)
theorem guard1027 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 202 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1027 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 202 .northEast = true) : bonus 227 p ≤ bonus 202 p := by
  have certified := compare103 p (guard1027 p guard)
  simpa only [at227, at202, Int.zero_add] using certified
theorem check1027 (p : Pattern) : (!walkGuard soko3_2.board support p 227 202 .northEast || decide (bonus 227 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound1027 p)
theorem guard1028 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 200 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1028 (p : Pattern) (guard : walkGuard soko3_2.board support p 227 200 .northWest = true) : bonus 227 p ≤ bonus 200 p := by
  have certified := compare103 p (guard1028 p guard)
  simpa only [at227, at200, Int.zero_add] using certified
theorem check1028 (p : Pattern) : (!walkGuard soko3_2.board support p 227 200 .northWest || decide (bonus 227 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound1028 p)
theorem guard1029 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 202 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1029 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 202 .north = true) : bonus 228 p ≤ bonus 202 p := by
  have certified := compare103 p (guard1029 p guard)
  simpa only [at228, at202, Int.zero_add] using certified
theorem check1029 (p : Pattern) : (!walkGuard soko3_2.board support p 228 202 .north || decide (bonus 228 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound1029 p)
theorem guard1030 (p : Pattern) (guard : pushGuard support p 228 202 176 176 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1030 (p : Pattern) (guard : pushGuard support p 228 202 176 176 = true) : bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some 176)) := by
  have certified := compare37 p (guard1030 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 202 (some 176))
  have normalized := agree0 _ _ (change_representative support p 202 (some 176) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1030 (p : Pattern) : (!pushGuard support p 228 202 176 176 || decide (bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some 176)))) = true :=
  check_of_implication _ _ (bound1030 p)
theorem guard1031 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 229 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1031 (p : Pattern) (guard : walkGuard soko3_2.board support p 228 229 .east = true) : bonus 228 p ≤ bonus 229 p := by
  have certified := compare103 p (guard1031 p guard)
  simpa only [at228, at229, Int.zero_add] using certified
theorem check1031 (p : Pattern) : (!walkGuard soko3_2.board support p 228 229 .east || decide (bonus 228 p ≤ bonus 229 p)) = true :=
  check_of_implication _ _ (bound1031 p)
end NetHack.Sokoban32Refined
