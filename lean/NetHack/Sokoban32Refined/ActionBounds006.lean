import NetHack.Sokoban32Refined.ActionBounds005
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard144 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 44 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound144 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 44 .north = true) : bonus 70 p ≤ bonus 44 p := by
  have certified := compare103 p (guard144 p guard)
  simpa only [at70, at44, Int.zero_add] using certified
theorem check144 (p : Pattern) : (!walkGuard soko3_2.board support p 70 44 .north || decide (bonus 70 p ≤ bonus 44 p)) = true :=
  check_of_implication _ _ (bound144 p)
theorem guard145 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 96 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound145 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 96 .south = true) : bonus 70 p ≤ bonus 96 p := by
  have certified := compare103 p (guard145 p guard)
  simpa only [at70, at96, Int.zero_add] using certified
theorem check145 (p : Pattern) : (!walkGuard soko3_2.board support p 70 96 .south || decide (bonus 70 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound145 p)
theorem guard146 (p : Pattern) (guard : pushGuard support p 70 96 122 122 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound146 (p : Pattern) (guard : pushGuard support p 70 96 122 122 = true) : bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some 122)) := by
  have certified := compare37 p (guard146 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 96 (some 122))
  have normalized := agree0 _ _ (change_representative support p 96 (some 122) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check146 (p : Pattern) : (!pushGuard support p 70 96 122 122 || decide (bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some 122)))) = true :=
  check_of_implication _ _ (bound146 p)
theorem guard147 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 71 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound147 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 71 .east = true) : bonus 70 p ≤ bonus 71 p := by
  have certified := compare103 p (guard147 p guard)
  simpa only [at70, at71, Int.zero_add] using certified
theorem check147 (p : Pattern) : (!walkGuard soko3_2.board support p 70 71 .east || decide (bonus 70 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound147 p)
theorem guard148 (p : Pattern) (guard : pushGuard support p 70 71 72 72 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound148 (p : Pattern) (guard : pushGuard support p 70 71 72 72 = true) : bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some 72)) := by
  have certified := compare37 p (guard148 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 71 (some 72))
  have normalized := agree0 _ _ (change_representative support p 71 (some 72) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check148 (p : Pattern) : (!pushGuard support p 70 71 72 72 || decide (bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some 72)))) = true :=
  check_of_implication _ _ (bound148 p)
theorem guard149 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 69 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound149 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 69 .west = true) : bonus 70 p ≤ bonus 69 p := by
  have certified := compare103 p (guard149 p guard)
  simpa only [at70, at69, Int.zero_add] using certified
theorem check149 (p : Pattern) : (!walkGuard soko3_2.board support p 70 69 .west || decide (bonus 70 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound149 p)
theorem guard150 (p : Pattern) (guard : pushGuard support p 70 69 68 68 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound150 (p : Pattern) (guard : pushGuard support p 70 69 68 68 = true) : bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder 68 - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some 68)) := by
  have certified := compare37 p (guard150 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 69 (some 68))
  have normalized := agree0 _ _ (change_representative support p 69 (some 68) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check150 (p : Pattern) : (!pushGuard support p 70 69 68 68 || decide (bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder 68 - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some 68)))) = true :=
  check_of_implication _ _ (bound150 p)
theorem guard151 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 45 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound151 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 45 .northEast = true) : bonus 70 p ≤ bonus 45 p := by
  have certified := compare103 p (guard151 p guard)
  simpa only [at70, at45, Int.zero_add] using certified
theorem check151 (p : Pattern) : (!walkGuard soko3_2.board support p 70 45 .northEast || decide (bonus 70 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound151 p)
theorem guard152 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 43 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound152 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 43 .northWest = true) : bonus 70 p ≤ bonus 43 p := by
  have certified := compare103 p (guard152 p guard)
  simpa only [at70, at43, Int.zero_add] using certified
theorem check152 (p : Pattern) : (!walkGuard soko3_2.board support p 70 43 .northWest || decide (bonus 70 p ≤ bonus 43 p)) = true :=
  check_of_implication _ _ (bound152 p)
theorem guard153 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 97 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound153 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 97 .southEast = true) : bonus 70 p ≤ bonus 97 p := by
  have certified := compare103 p (guard153 p guard)
  simpa only [at70, at97, Int.zero_add] using certified
theorem check153 (p : Pattern) : (!walkGuard soko3_2.board support p 70 97 .southEast || decide (bonus 70 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound153 p)
theorem guard154 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 95 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound154 (p : Pattern) (guard : walkGuard soko3_2.board support p 70 95 .southWest = true) : bonus 70 p ≤ bonus 95 p := by
  have certified := compare103 p (guard154 p guard)
  simpa only [at70, at95, Int.zero_add] using certified
theorem check154 (p : Pattern) : (!walkGuard soko3_2.board support p 70 95 .southWest || decide (bonus 70 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound154 p)
theorem guard155 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 45 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound155 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 45 .north = true) : bonus 71 p ≤ bonus 45 p := by
  have certified := compare103 p (guard155 p guard)
  simpa only [at71, at45, Int.zero_add] using certified
theorem check155 (p : Pattern) : (!walkGuard soko3_2.board support p 71 45 .north || decide (bonus 71 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound155 p)
theorem guard156 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 97 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound156 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 97 .south = true) : bonus 71 p ≤ bonus 97 p := by
  have certified := compare103 p (guard156 p guard)
  simpa only [at71, at97, Int.zero_add] using certified
theorem check156 (p : Pattern) : (!walkGuard soko3_2.board support p 71 97 .south || decide (bonus 71 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound156 p)
theorem guard157 (p : Pattern) (guard : pushGuard support p 71 97 123 123 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound157 (p : Pattern) (guard : pushGuard support p 71 97 123 123 = true) : bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some 123)) := by
  have certified := compare37 p (guard157 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 97 (some 123))
  have normalized := agree0 _ _ (change_representative support p 97 (some 123) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check157 (p : Pattern) : (!pushGuard support p 71 97 123 123 || decide (bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some 123)))) = true :=
  check_of_implication _ _ (bound157 p)
theorem guard158 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 72 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound158 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 72 .east = true) : bonus 71 p ≤ bonus 72 p := by
  have certified := compare103 p (guard158 p guard)
  simpa only [at71, at72, Int.zero_add] using certified
theorem check158 (p : Pattern) : (!walkGuard soko3_2.board support p 71 72 .east || decide (bonus 71 p ≤ bonus 72 p)) = true :=
  check_of_implication _ _ (bound158 p)
theorem guard159 (p : Pattern) (guard : pushGuard support p 71 72 73 73 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound159 (p : Pattern) (guard : pushGuard support p 71 72 73 73 = true) : bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some 73)) := by
  have certified := compare37 p (guard159 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 72 (some 73))
  have normalized := agree0 _ _ (change_representative support p 72 (some 73) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check159 (p : Pattern) : (!pushGuard support p 71 72 73 73 || decide (bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some 73)))) = true :=
  check_of_implication _ _ (bound159 p)
theorem guard160 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 70 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound160 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 70 .west = true) : bonus 71 p ≤ bonus 70 p := by
  have certified := compare103 p (guard160 p guard)
  simpa only [at71, at70, Int.zero_add] using certified
theorem check160 (p : Pattern) : (!walkGuard soko3_2.board support p 71 70 .west || decide (bonus 71 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound160 p)
theorem guard161 (p : Pattern) (guard : pushGuard support p 71 70 69 69 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound161 (p : Pattern) (guard : pushGuard support p 71 70 69 69 = true) : bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder 69 - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some 69)) := by
  have certified := compare37 p (guard161 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 70 (some 69))
  have normalized := agree0 _ _ (change_representative support p 70 (some 69) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check161 (p : Pattern) : (!pushGuard support p 71 70 69 69 || decide (bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder 69 - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some 69)))) = true :=
  check_of_implication _ _ (bound161 p)
theorem guard162 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 46 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound162 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 46 .northEast = true) : bonus 71 p ≤ bonus 46 p := by
  have certified := compare103 p (guard162 p guard)
  simpa only [at71, at46, Int.zero_add] using certified
theorem check162 (p : Pattern) : (!walkGuard soko3_2.board support p 71 46 .northEast || decide (bonus 71 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound162 p)
theorem guard163 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 44 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound163 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 44 .northWest = true) : bonus 71 p ≤ bonus 44 p := by
  have certified := compare103 p (guard163 p guard)
  simpa only [at71, at44, Int.zero_add] using certified
theorem check163 (p : Pattern) : (!walkGuard soko3_2.board support p 71 44 .northWest || decide (bonus 71 p ≤ bonus 44 p)) = true :=
  check_of_implication _ _ (bound163 p)
theorem guard164 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 98 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound164 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 98 .southEast = true) : bonus 71 p ≤ bonus 98 p := by
  have certified := compare103 p (guard164 p guard)
  simpa only [at71, at98, Int.zero_add] using certified
theorem check164 (p : Pattern) : (!walkGuard soko3_2.board support p 71 98 .southEast || decide (bonus 71 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound164 p)
theorem guard165 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 96 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound165 (p : Pattern) (guard : walkGuard soko3_2.board support p 71 96 .southWest = true) : bonus 71 p ≤ bonus 96 p := by
  have certified := compare103 p (guard165 p guard)
  simpa only [at71, at96, Int.zero_add] using certified
theorem check165 (p : Pattern) : (!walkGuard soko3_2.board support p 71 96 .southWest || decide (bonus 71 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound165 p)
theorem guard166 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 46 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound166 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 46 .north = true) : bonus 72 p ≤ bonus 46 p := by
  have certified := compare103 p (guard166 p guard)
  simpa only [at72, at46, Int.zero_add] using certified
theorem check166 (p : Pattern) : (!walkGuard soko3_2.board support p 72 46 .north || decide (bonus 72 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound166 p)
theorem guard167 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 98 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound167 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 98 .south = true) : bonus 72 p ≤ bonus 98 p := by
  have certified := compare103 p (guard167 p guard)
  simpa only [at72, at98, Int.zero_add] using certified
theorem check167 (p : Pattern) : (!walkGuard soko3_2.board support p 72 98 .south || decide (bonus 72 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound167 p)
end NetHack.Sokoban32Refined
