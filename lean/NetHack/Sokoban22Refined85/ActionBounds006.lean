import NetHack.Sokoban22Refined85.ActionBounds005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard144 (p : Pattern) (guard : pushGuard support p 79 101 123 123 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound144 (p : Pattern) (guard : pushGuard support p 79 101 123 123 = true) : bonus 79 p ≤ 1 + Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some 123)) := by
  have certified := compare1087 p (guard144 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 101 (some 123))
  have normalized := agree0 _ _ (change_representative support p 101 (some 123) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check144 (p : Pattern) : (!pushGuard support p 79 101 123 123 || decide (bonus 79 p ≤ 1 + Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some 123)))) = true :=
  check_of_implication _ _ (bound144 p)
theorem guard145 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 80 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound145 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 80 .east = true) : bonus 79 p ≤ bonus 80 p := by
  have certified := compare1086 p (guard145 p guard)
  simpa only [at79, at80, Int.zero_add] using certified
theorem check145 (p : Pattern) : (!walkGuard soko2_2.board support p 79 80 .east || decide (bonus 79 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound145 p)
theorem guard146 (p : Pattern) (guard : pushGuard support p 79 80 81 81 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound146 (p : Pattern) (guard : pushGuard support p 79 80 81 81 = true) : bonus 79 p ≤ 1 + Generated.soko2_2Potential.boulder 81 - Generated.soko2_2Potential.boulder 80 + bonus 80 (change p 80 (some 81)) := by
  have certified := compare1087 p (guard146 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 80 (some 81))
  have normalized := agree0 _ _ (change_representative support p 80 (some 81) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check146 (p : Pattern) : (!pushGuard support p 79 80 81 81 || decide (bonus 79 p ≤ 1 + Generated.soko2_2Potential.boulder 81 - Generated.soko2_2Potential.boulder 80 + bonus 80 (change p 80 (some 81)))) = true :=
  check_of_implication _ _ (bound146 p)
theorem guard147 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 78 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound147 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 78 .west = true) : bonus 79 p ≤ bonus 78 p := by
  have certified := compare1086 p (guard147 p guard)
  simpa only [at79, at78, Int.zero_add] using certified
theorem check147 (p : Pattern) : (!walkGuard soko2_2.board support p 79 78 .west || decide (bonus 79 p ≤ bonus 78 p)) = true :=
  check_of_implication _ _ (bound147 p)
theorem guard148 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 102 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound148 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 102 .southEast = true) : bonus 79 p ≤ bonus 102 p := by
  have certified := compare1086 p (guard148 p guard)
  simpa only [at79, at102, Int.zero_add] using certified
theorem check148 (p : Pattern) : (!walkGuard soko2_2.board support p 79 102 .southEast || decide (bonus 79 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound148 p)
theorem guard149 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 100 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound149 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 100 .southWest = true) : bonus 79 p ≤ bonus 100 p := by
  have certified := compare1086 p (guard149 p guard)
  simpa only [at79, at100, Int.zero_add] using certified
theorem check149 (p : Pattern) : (!walkGuard soko2_2.board support p 79 100 .southWest || decide (bonus 79 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound149 p)
theorem guard150 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 102 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound150 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 102 .south = true) : bonus 80 p ≤ bonus 102 p := by
  have certified := compare1086 p (guard150 p guard)
  simpa only [at80, at102, Int.zero_add] using certified
theorem check150 (p : Pattern) : (!walkGuard soko2_2.board support p 80 102 .south || decide (bonus 80 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound150 p)
theorem guard151 (p : Pattern) (guard : pushGuard support p 80 102 124 124 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound151 (p : Pattern) (guard : pushGuard support p 80 102 124 124 = true) : bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some 124)) := by
  have certified := compare1087 p (guard151 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 102 (some 124))
  have normalized := agree0 _ _ (change_representative support p 102 (some 124) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check151 (p : Pattern) : (!pushGuard support p 80 102 124 124 || decide (bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some 124)))) = true :=
  check_of_implication _ _ (bound151 p)
theorem guard152 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 81 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound152 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 81 .east = true) : bonus 80 p ≤ bonus 81 p := by
  have certified := compare1086 p (guard152 p guard)
  simpa only [at80, at81, Int.zero_add] using certified
theorem check152 (p : Pattern) : (!walkGuard soko2_2.board support p 80 81 .east || decide (bonus 80 p ≤ bonus 81 p)) = true :=
  check_of_implication _ _ (bound152 p)
theorem guard153 (p : Pattern) (guard : pushGuard support p 80 81 82 82 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound153 (p : Pattern) (guard : pushGuard support p 80 81 82 82 = true) : bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder 82 - Generated.soko2_2Potential.boulder 81 + bonus 81 (change p 81 (some 82)) := by
  have certified := compare1087 p (guard153 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 81 (some 82))
  have normalized := agree0 _ _ (change_representative support p 81 (some 82) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check153 (p : Pattern) : (!pushGuard support p 80 81 82 82 || decide (bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder 82 - Generated.soko2_2Potential.boulder 81 + bonus 81 (change p 81 (some 82)))) = true :=
  check_of_implication _ _ (bound153 p)
theorem guard154 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 79 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound154 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 79 .west = true) : bonus 80 p ≤ bonus 79 p := by
  have certified := compare1086 p (guard154 p guard)
  simpa only [at80, at79, Int.zero_add] using certified
theorem check154 (p : Pattern) : (!walkGuard soko2_2.board support p 80 79 .west || decide (bonus 80 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound154 p)
theorem guard155 (p : Pattern) (guard : pushGuard support p 80 79 78 78 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound155 (p : Pattern) (guard : pushGuard support p 80 79 78 78 = true) : bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder 78 - Generated.soko2_2Potential.boulder 79 + bonus 79 (change p 79 (some 78)) := by
  have certified := compare1087 p (guard155 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 79 (some 78))
  have normalized := agree0 _ _ (change_representative support p 79 (some 78) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check155 (p : Pattern) : (!pushGuard support p 80 79 78 78 || decide (bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder 78 - Generated.soko2_2Potential.boulder 79 + bonus 79 (change p 79 (some 78)))) = true :=
  check_of_implication _ _ (bound155 p)
theorem guard156 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 103 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound156 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 103 .southEast = true) : bonus 80 p ≤ bonus 103 p := by
  have certified := compare1086 p (guard156 p guard)
  simpa only [at80, at103, Int.zero_add] using certified
theorem check156 (p : Pattern) : (!walkGuard soko2_2.board support p 80 103 .southEast || decide (bonus 80 p ≤ bonus 103 p)) = true :=
  check_of_implication _ _ (bound156 p)
theorem guard157 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 101 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound157 (p : Pattern) (guard : walkGuard soko2_2.board support p 80 101 .southWest = true) : bonus 80 p ≤ bonus 101 p := by
  have certified := compare1086 p (guard157 p guard)
  simpa only [at80, at101, Int.zero_add] using certified
theorem check157 (p : Pattern) : (!walkGuard soko2_2.board support p 80 101 .southWest || decide (bonus 80 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound157 p)
theorem guard158 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 103 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound158 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 103 .south = true) : bonus 81 p ≤ bonus 103 p := by
  have certified := compare1086 p (guard158 p guard)
  simpa only [at81, at103, Int.zero_add] using certified
theorem check158 (p : Pattern) : (!walkGuard soko2_2.board support p 81 103 .south || decide (bonus 81 p ≤ bonus 103 p)) = true :=
  check_of_implication _ _ (bound158 p)
theorem guard159 (p : Pattern) (guard : pushGuard support p 81 103 125 125 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound159 (p : Pattern) (guard : pushGuard support p 81 103 125 125 = true) : bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some 125)) := by
  have certified := compare1087 p (guard159 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 103 (some 125))
  have normalized := agree0 _ _ (change_representative support p 103 (some 125) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check159 (p : Pattern) : (!pushGuard support p 81 103 125 125 || decide (bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some 125)))) = true :=
  check_of_implication _ _ (bound159 p)
theorem guard160 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 82 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound160 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 82 .east = true) : bonus 81 p ≤ bonus 82 p := by
  have certified := compare1086 p (guard160 p guard)
  simpa only [at81, at82, Int.zero_add] using certified
theorem check160 (p : Pattern) : (!walkGuard soko2_2.board support p 81 82 .east || decide (bonus 81 p ≤ bonus 82 p)) = true :=
  check_of_implication _ _ (bound160 p)
theorem guard161 (p : Pattern) (guard : pushGuard support p 81 82 83 83 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound161 (p : Pattern) (guard : pushGuard support p 81 82 83 83 = true) : bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder 83 - Generated.soko2_2Potential.boulder 82 + bonus 82 (change p 82 (some 83)) := by
  have certified := compare1087 p (guard161 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 82 (some 83))
  have normalized := agree0 _ _ (change_representative support p 82 (some 83) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check161 (p : Pattern) : (!pushGuard support p 81 82 83 83 || decide (bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder 83 - Generated.soko2_2Potential.boulder 82 + bonus 82 (change p 82 (some 83)))) = true :=
  check_of_implication _ _ (bound161 p)
theorem guard162 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 80 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound162 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 80 .west = true) : bonus 81 p ≤ bonus 80 p := by
  have certified := compare1086 p (guard162 p guard)
  simpa only [at81, at80, Int.zero_add] using certified
theorem check162 (p : Pattern) : (!walkGuard soko2_2.board support p 81 80 .west || decide (bonus 81 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound162 p)
theorem guard163 (p : Pattern) (guard : pushGuard support p 81 80 79 79 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound163 (p : Pattern) (guard : pushGuard support p 81 80 79 79 = true) : bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder 79 - Generated.soko2_2Potential.boulder 80 + bonus 80 (change p 80 (some 79)) := by
  have certified := compare1087 p (guard163 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 80 (some 79))
  have normalized := agree0 _ _ (change_representative support p 80 (some 79) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check163 (p : Pattern) : (!pushGuard support p 81 80 79 79 || decide (bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder 79 - Generated.soko2_2Potential.boulder 80 + bonus 80 (change p 80 (some 79)))) = true :=
  check_of_implication _ _ (bound163 p)
theorem guard164 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 104 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound164 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 104 .southEast = true) : bonus 81 p ≤ bonus 104 p := by
  have certified := compare1086 p (guard164 p guard)
  simpa only [at81, at104, Int.zero_add] using certified
theorem check164 (p : Pattern) : (!walkGuard soko2_2.board support p 81 104 .southEast || decide (bonus 81 p ≤ bonus 104 p)) = true :=
  check_of_implication _ _ (bound164 p)
theorem guard165 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 102 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound165 (p : Pattern) (guard : walkGuard soko2_2.board support p 81 102 .southWest = true) : bonus 81 p ≤ bonus 102 p := by
  have certified := compare1086 p (guard165 p guard)
  simpa only [at81, at102, Int.zero_add] using certified
theorem check165 (p : Pattern) : (!walkGuard soko2_2.board support p 81 102 .southWest || decide (bonus 81 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound165 p)
theorem guard166 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 104 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound166 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 104 .south = true) : bonus 82 p ≤ bonus 104 p := by
  have certified := compare1086 p (guard166 p guard)
  simpa only [at82, at104, Int.zero_add] using certified
theorem check166 (p : Pattern) : (!walkGuard soko2_2.board support p 82 104 .south || decide (bonus 82 p ≤ bonus 104 p)) = true :=
  check_of_implication _ _ (bound166 p)
theorem guard167 (p : Pattern) (guard : pushGuard support p 82 104 126 126 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound167 (p : Pattern) (guard : pushGuard support p 82 104 126 126 = true) : bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some 126)) := by
  have certified := compare1087 p (guard167 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 104 (some 126))
  have normalized := agree0 _ _ (change_representative support p 104 (some 126) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check167 (p : Pattern) : (!pushGuard support p 82 104 126 126 || decide (bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some 126)))) = true :=
  check_of_implication _ _ (bound167 p)
end NetHack.Sokoban22Refined85
