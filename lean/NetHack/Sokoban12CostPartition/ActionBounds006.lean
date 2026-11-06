import NetHack.Sokoban12CostPartition.ActionBounds005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard144 (p : Pattern) (guard : pushGuard support p 50 49 48 48 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound144 (p : Pattern) (guard : pushGuard support p 50 49 48 48 = true) : bonus 50 p ≤ 1 - Generated.soko1_2Potential.boulder 49 - Generated.soko1_2Potential.hole 48 + bonus 49 (change p 49 none) := by
  have certified := compare3 p (guard144 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 49 none)
  have normalized := agree75 _ _ (change_representative support p 49 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check144 (p : Pattern) : (!pushGuard support p 50 49 48 48 || decide (bonus 50 p ≤ 1 - Generated.soko1_2Potential.boulder 49 - Generated.soko1_2Potential.hole 48 + bonus 49 (change p 49 none))) = true :=
  check_of_implication _ _ (bound144 p)
theorem guard145 (p : Pattern) (guard : walkGuard soko1_2.board support p 55 29 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound145 (p : Pattern) (guard : walkGuard soko1_2.board support p 55 29 .north = true) : bonus 55 p ≤ bonus 29 p := by
  have certified := compare0 p (guard145 p guard)
  simpa only [at55, at29, Int.zero_add] using certified
theorem check145 (p : Pattern) : (!walkGuard soko1_2.board support p 55 29 .north || decide (bonus 55 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound145 p)
theorem guard146 (p : Pattern) (guard : walkGuard soko1_2.board support p 55 56 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound146 (p : Pattern) (guard : walkGuard soko1_2.board support p 55 56 .east = true) : bonus 55 p ≤ bonus 56 p := by
  have certified := compare0 p (guard146 p guard)
  simpa only [at55, at56, Int.zero_add] using certified
theorem check146 (p : Pattern) : (!walkGuard soko1_2.board support p 55 56 .east || decide (bonus 55 p ≤ bonus 56 p)) = true :=
  check_of_implication _ _ (bound146 p)
theorem guard147 (p : Pattern) (guard : walkGuard soko1_2.board support p 55 30 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound147 (p : Pattern) (guard : walkGuard soko1_2.board support p 55 30 .northEast = true) : bonus 55 p ≤ bonus 30 p := by
  have certified := compare0 p (guard147 p guard)
  simpa only [at55, at30, Int.zero_add] using certified
theorem check147 (p : Pattern) : (!walkGuard soko1_2.board support p 55 30 .northEast || decide (bonus 55 p ≤ bonus 30 p)) = true :=
  check_of_implication _ _ (bound147 p)
theorem guard148 (p : Pattern) (guard : walkGuard soko1_2.board support p 55 82 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound148 (p : Pattern) (guard : walkGuard soko1_2.board support p 55 82 .southEast = true) : bonus 55 p ≤ bonus 82 p := by
  have certified := compare0 p (guard148 p guard)
  simpa only [at55, at82, Int.zero_add] using certified
theorem check148 (p : Pattern) : (!walkGuard soko1_2.board support p 55 82 .southEast || decide (bonus 55 p ≤ bonus 82 p)) = true :=
  check_of_implication _ _ (bound148 p)
theorem guard149 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 30 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound149 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 30 .north = true) : bonus 56 p ≤ bonus 30 p := by
  have certified := compare0 p (guard149 p guard)
  simpa only [at56, at30, Int.zero_add] using certified
theorem check149 (p : Pattern) : (!walkGuard soko1_2.board support p 56 30 .north || decide (bonus 56 p ≤ bonus 30 p)) = true :=
  check_of_implication _ _ (bound149 p)
theorem guard150 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 82 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound150 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 82 .south = true) : bonus 56 p ≤ bonus 82 p := by
  have certified := compare0 p (guard150 p guard)
  simpa only [at56, at82, Int.zero_add] using certified
theorem check150 (p : Pattern) : (!walkGuard soko1_2.board support p 56 82 .south || decide (bonus 56 p ≤ bonus 82 p)) = true :=
  check_of_implication _ _ (bound150 p)
theorem guard151 (p : Pattern) (guard : pushGuard support p 56 82 108 108 = true) : d735 p = 1 := by
  change (!false && (!false || false) && !(p 108) && (!(p 108) || false)) = true at guard
  cases h108 : p 108
  all_goals simp [d0, d1, d735, h108] at guard ⊢
theorem bound151 (p : Pattern) (guard : pushGuard support p 56 82 108 108 = true) : bonus 56 p ≤ 1 + Generated.soko1_2Potential.boulder 108 - Generated.soko1_2Potential.boulder 82 + bonus 82 (change p 82 (some 108)) := by
  have certified := compare35 p (guard151 p guard)
  change d75 p ≤ (2 : Int) + d75 (change p 82 (some 108))
  have normalized := agree75 _ _ (change_representative support p 82 (some 108) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (2 : Int) + d75 (change p 10000 (some 108))
  rw [sub47]
  exact certified
theorem check151 (p : Pattern) : (!pushGuard support p 56 82 108 108 || decide (bonus 56 p ≤ 1 + Generated.soko1_2Potential.boulder 108 - Generated.soko1_2Potential.boulder 82 + bonus 82 (change p 82 (some 108)))) = true :=
  check_of_implication _ _ (bound151 p)
theorem guard152 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 55 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound152 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 55 .west = true) : bonus 56 p ≤ bonus 55 p := by
  have certified := compare0 p (guard152 p guard)
  simpa only [at56, at55, Int.zero_add] using certified
theorem check152 (p : Pattern) : (!walkGuard soko1_2.board support p 56 55 .west || decide (bonus 56 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound152 p)
theorem guard153 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 31 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound153 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 31 .northEast = true) : bonus 56 p ≤ bonus 31 p := by
  have certified := compare0 p (guard153 p guard)
  simpa only [at56, at31, Int.zero_add] using certified
theorem check153 (p : Pattern) : (!walkGuard soko1_2.board support p 56 31 .northEast || decide (bonus 56 p ≤ bonus 31 p)) = true :=
  check_of_implication _ _ (bound153 p)
theorem guard154 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 29 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound154 (p : Pattern) (guard : walkGuard soko1_2.board support p 56 29 .northWest = true) : bonus 56 p ≤ bonus 29 p := by
  have certified := compare0 p (guard154 p guard)
  simpa only [at56, at29, Int.zero_add] using certified
theorem check154 (p : Pattern) : (!walkGuard soko1_2.board support p 56 29 .northWest || decide (bonus 56 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound154 p)
theorem guard155 (p : Pattern) (guard : walkGuard soko1_2.board support p 76 50 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound155 (p : Pattern) (guard : walkGuard soko1_2.board support p 76 50 .north = true) : bonus 76 p ≤ bonus 50 p := by
  have certified := compare0 p (guard155 p guard)
  simpa only [at76, at50, Int.zero_add] using certified
theorem check155 (p : Pattern) : (!walkGuard soko1_2.board support p 76 50 .north || decide (bonus 76 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound155 p)
theorem guard156 (p : Pattern) (guard : walkGuard soko1_2.board support p 76 102 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound156 (p : Pattern) (guard : walkGuard soko1_2.board support p 76 102 .south = true) : bonus 76 p ≤ bonus 102 p := by
  have certified := compare0 p (guard156 p guard)
  simpa only [at76, at102, Int.zero_add] using certified
theorem check156 (p : Pattern) : (!walkGuard soko1_2.board support p 76 102 .south || decide (bonus 76 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound156 p)
theorem guard157 (p : Pattern) (guard : pushGuard support p 76 102 128 128 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound157 (p : Pattern) (guard : pushGuard support p 76 102 128 128 = true) : bonus 76 p ≤ 1 + Generated.soko1_2Potential.boulder 128 - Generated.soko1_2Potential.boulder 102 + bonus 102 (change p 102 (some 128)) := by
  have certified := compare3 p (guard157 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 102 (some 128))
  have normalized := agree75 _ _ (change_representative support p 102 (some 128) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check157 (p : Pattern) : (!pushGuard support p 76 102 128 128 || decide (bonus 76 p ≤ 1 + Generated.soko1_2Potential.boulder 128 - Generated.soko1_2Potential.boulder 102 + bonus 102 (change p 102 (some 128)))) = true :=
  check_of_implication _ _ (bound157 p)
theorem guard158 (p : Pattern) (guard : walkGuard soko1_2.board support p 76 49 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound158 (p : Pattern) (guard : walkGuard soko1_2.board support p 76 49 .northWest = true) : bonus 76 p ≤ bonus 49 p := by
  have certified := compare0 p (guard158 p guard)
  simpa only [at76, at49, Int.zero_add] using certified
theorem check158 (p : Pattern) : (!walkGuard soko1_2.board support p 76 49 .northWest || decide (bonus 76 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound158 p)
theorem guard159 (p : Pattern) (guard : walkGuard soko1_2.board support p 82 56 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound159 (p : Pattern) (guard : walkGuard soko1_2.board support p 82 56 .north = true) : bonus 82 p ≤ bonus 56 p := by
  have certified := compare0 p (guard159 p guard)
  simpa only [at82, at56, Int.zero_add] using certified
theorem check159 (p : Pattern) : (!walkGuard soko1_2.board support p 82 56 .north || decide (bonus 82 p ≤ bonus 56 p)) = true :=
  check_of_implication _ _ (bound159 p)
theorem guard160 (p : Pattern) (guard : pushGuard support p 82 56 30 30 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound160 (p : Pattern) (guard : pushGuard support p 82 56 30 30 = true) : bonus 82 p ≤ 1 + Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.boulder 56 + bonus 56 (change p 56 (some 30)) := by
  have certified := compare0 p (guard160 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 56 (some 30))
  have normalized := agree75 _ _ (change_representative support p 56 (some 30) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check160 (p : Pattern) : (!pushGuard support p 82 56 30 30 || decide (bonus 82 p ≤ 1 + Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.boulder 56 + bonus 56 (change p 56 (some 30)))) = true :=
  check_of_implication _ _ (bound160 p)
theorem guard161 (p : Pattern) (guard : walkGuard soko1_2.board support p 82 108 .south = true) : d735 p = 1 := by
  change (!false && !(p 108) && !false) = true at guard
  cases h108 : p 108
  all_goals simp [d0, d1, d735, h108] at guard ⊢
theorem bound161 (p : Pattern) (guard : walkGuard soko1_2.board support p 82 108 .south = true) : bonus 82 p ≤ bonus 108 p := by
  have certified := compare36 p (guard161 p guard)
  simpa only [at82, at108, Int.zero_add] using certified
theorem check161 (p : Pattern) : (!walkGuard soko1_2.board support p 82 108 .south || decide (bonus 82 p ≤ bonus 108 p)) = true :=
  check_of_implication _ _ (bound161 p)
theorem guard162 (p : Pattern) (guard : pushGuard support p 82 108 134 134 = true) : d738 p = 1 := by
  change (!false && (!true || (p 108)) && !(p 134) && (!(p 134) || false)) = true at guard
  cases h108 : p 108 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d738, h108, h134] at guard ⊢
theorem bound162 (p : Pattern) (guard : pushGuard support p 82 108 134 134 = true) : bonus 82 p ≤ 1 + Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.boulder 108 + bonus 108 (change p 108 (some 134)) := by
  have certified := compare39 p (guard162 p guard)
  change d75 p ≤ (2 : Int) + d75 (change p 108 (some 134))
  have normalized := agree75 _ _ (change_representative support p 108 (some 134) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (2 : Int) + d75 (change p 108 (some 134))
  rw [sub65]
  exact certified
theorem check162 (p : Pattern) : (!pushGuard support p 82 108 134 134 || decide (bonus 82 p ≤ 1 + Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.boulder 108 + bonus 108 (change p 108 (some 134)))) = true :=
  check_of_implication _ _ (bound162 p)
theorem guard163 (p : Pattern) (guard : walkGuard soko1_2.board support p 82 55 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound163 (p : Pattern) (guard : walkGuard soko1_2.board support p 82 55 .northWest = true) : bonus 82 p ≤ bonus 55 p := by
  have certified := compare0 p (guard163 p guard)
  simpa only [at82, at55, Int.zero_add] using certified
theorem check163 (p : Pattern) : (!walkGuard soko1_2.board support p 82 55 .northWest || decide (bonus 82 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound163 p)
theorem guard164 (p : Pattern) (guard : walkGuard soko1_2.board support p 102 76 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound164 (p : Pattern) (guard : walkGuard soko1_2.board support p 102 76 .north = true) : bonus 102 p ≤ bonus 76 p := by
  have certified := compare0 p (guard164 p guard)
  simpa only [at102, at76, Int.zero_add] using certified
theorem check164 (p : Pattern) : (!walkGuard soko1_2.board support p 102 76 .north || decide (bonus 102 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound164 p)
theorem guard165 (p : Pattern) (guard : pushGuard support p 102 76 50 50 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound165 (p : Pattern) (guard : pushGuard support p 102 76 50 50 = true) : bonus 102 p ≤ 1 + Generated.soko1_2Potential.boulder 50 - Generated.soko1_2Potential.boulder 76 + bonus 76 (change p 76 (some 50)) := by
  have certified := compare3 p (guard165 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 76 (some 50))
  have normalized := agree75 _ _ (change_representative support p 76 (some 50) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check165 (p : Pattern) : (!pushGuard support p 102 76 50 50 || decide (bonus 102 p ≤ 1 + Generated.soko1_2Potential.boulder 50 - Generated.soko1_2Potential.boulder 76 + bonus 76 (change p 76 (some 50)))) = true :=
  check_of_implication _ _ (bound165 p)
theorem guard166 (p : Pattern) (guard : walkGuard soko1_2.board support p 102 128 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound166 (p : Pattern) (guard : walkGuard soko1_2.board support p 102 128 .south = true) : bonus 102 p ≤ bonus 128 p := by
  have certified := compare0 p (guard166 p guard)
  simpa only [at102, at128, Int.zero_add] using certified
theorem check166 (p : Pattern) : (!walkGuard soko1_2.board support p 102 128 .south || decide (bonus 102 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound166 p)
theorem guard167 (p : Pattern) (guard : pushGuard support p 102 128 154 154 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound167 (p : Pattern) (guard : pushGuard support p 102 128 154 154 = true) : bonus 102 p ≤ 1 + Generated.soko1_2Potential.boulder 154 - Generated.soko1_2Potential.boulder 128 + bonus 128 (change p 128 (some 154)) := by
  have certified := compare3 p (guard167 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 128 (some 154))
  have normalized := agree75 _ _ (change_representative support p 128 (some 154) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check167 (p : Pattern) : (!pushGuard support p 102 128 154 154 || decide (bonus 102 p ≤ 1 + Generated.soko1_2Potential.boulder 154 - Generated.soko1_2Potential.boulder 128 + bonus 128 (change p 128 (some 154)))) = true :=
  check_of_implication _ _ (bound167 p)
end NetHack.Sokoban12CostPartition
