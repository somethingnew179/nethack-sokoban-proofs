import NetHack.Sokoban32Refined.ActionBounds007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard192 (p : Pattern) (guard : pushGuard support p 74 75 76 76 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound192 (p : Pattern) (guard : pushGuard support p 74 75 76 76 = true) : bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder 76 - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some 76)) := by
  have certified := compare37 p (guard192 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 75 (some 76))
  have normalized := agree0 _ _ (change_representative support p 75 (some 76) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check192 (p : Pattern) : (!pushGuard support p 74 75 76 76 || decide (bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder 76 - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some 76)))) = true :=
  check_of_implication _ _ (bound192 p)
theorem guard193 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 73 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound193 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 73 .west = true) : bonus 74 p ≤ bonus 73 p := by
  have certified := compare103 p (guard193 p guard)
  simpa only [at74, at73, Int.zero_add] using certified
theorem check193 (p : Pattern) : (!walkGuard soko3_2.board support p 74 73 .west || decide (bonus 74 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound193 p)
theorem guard194 (p : Pattern) (guard : pushGuard support p 74 73 72 72 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound194 (p : Pattern) (guard : pushGuard support p 74 73 72 72 = true) : bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some 72)) := by
  have certified := compare37 p (guard194 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 73 (some 72))
  have normalized := agree0 _ _ (change_representative support p 73 (some 72) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check194 (p : Pattern) : (!pushGuard support p 74 73 72 72 || decide (bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some 72)))) = true :=
  check_of_implication _ _ (bound194 p)
theorem guard195 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 49 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound195 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 49 .northEast = true) : bonus 74 p ≤ bonus 49 p := by
  have certified := compare103 p (guard195 p guard)
  simpa only [at74, at49, Int.zero_add] using certified
theorem check195 (p : Pattern) : (!walkGuard soko3_2.board support p 74 49 .northEast || decide (bonus 74 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound195 p)
theorem guard196 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 47 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound196 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 47 .northWest = true) : bonus 74 p ≤ bonus 47 p := by
  have certified := compare103 p (guard196 p guard)
  simpa only [at74, at47, Int.zero_add] using certified
theorem check196 (p : Pattern) : (!walkGuard soko3_2.board support p 74 47 .northWest || decide (bonus 74 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound196 p)
theorem guard197 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 101 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound197 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 101 .southEast = true) : bonus 74 p ≤ bonus 101 p := by
  have certified := compare103 p (guard197 p guard)
  simpa only [at74, at101, Int.zero_add] using certified
theorem check197 (p : Pattern) : (!walkGuard soko3_2.board support p 74 101 .southEast || decide (bonus 74 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound197 p)
theorem guard198 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 99 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound198 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 99 .southWest = true) : bonus 74 p ≤ bonus 99 p := by
  have certified := compare103 p (guard198 p guard)
  simpa only [at74, at99, Int.zero_add] using certified
theorem check198 (p : Pattern) : (!walkGuard soko3_2.board support p 74 99 .southWest || decide (bonus 74 p ≤ bonus 99 p)) = true :=
  check_of_implication _ _ (bound198 p)
theorem guard199 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 49 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound199 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 49 .north = true) : bonus 75 p ≤ bonus 49 p := by
  have certified := compare103 p (guard199 p guard)
  simpa only [at75, at49, Int.zero_add] using certified
theorem check199 (p : Pattern) : (!walkGuard soko3_2.board support p 75 49 .north || decide (bonus 75 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound199 p)
theorem guard200 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 101 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound200 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 101 .south = true) : bonus 75 p ≤ bonus 101 p := by
  have certified := compare103 p (guard200 p guard)
  simpa only [at75, at101, Int.zero_add] using certified
theorem check200 (p : Pattern) : (!walkGuard soko3_2.board support p 75 101 .south || decide (bonus 75 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound200 p)
theorem guard201 (p : Pattern) (guard : pushGuard support p 75 101 127 127 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound201 (p : Pattern) (guard : pushGuard support p 75 101 127 127 = true) : bonus 75 p ≤ 1 + Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some 127)) := by
  have certified := compare37 p (guard201 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 101 (some 127))
  have normalized := agree0 _ _ (change_representative support p 101 (some 127) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check201 (p : Pattern) : (!pushGuard support p 75 101 127 127 || decide (bonus 75 p ≤ 1 + Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some 127)))) = true :=
  check_of_implication _ _ (bound201 p)
theorem guard202 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 76 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound202 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 76 .east = true) : bonus 75 p ≤ bonus 76 p := by
  have certified := compare103 p (guard202 p guard)
  simpa only [at75, at76, Int.zero_add] using certified
theorem check202 (p : Pattern) : (!walkGuard soko3_2.board support p 75 76 .east || decide (bonus 75 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound202 p)
theorem guard203 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 74 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound203 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 74 .west = true) : bonus 75 p ≤ bonus 74 p := by
  have certified := compare103 p (guard203 p guard)
  simpa only [at75, at74, Int.zero_add] using certified
theorem check203 (p : Pattern) : (!walkGuard soko3_2.board support p 75 74 .west || decide (bonus 75 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound203 p)
theorem guard204 (p : Pattern) (guard : pushGuard support p 75 74 73 73 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound204 (p : Pattern) (guard : pushGuard support p 75 74 73 73 = true) : bonus 75 p ≤ 1 + Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some 73)) := by
  have certified := compare37 p (guard204 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 74 (some 73))
  have normalized := agree0 _ _ (change_representative support p 74 (some 73) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check204 (p : Pattern) : (!pushGuard support p 75 74 73 73 || decide (bonus 75 p ≤ 1 + Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some 73)))) = true :=
  check_of_implication _ _ (bound204 p)
theorem guard205 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 50 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound205 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 50 .northEast = true) : bonus 75 p ≤ bonus 50 p := by
  have certified := compare103 p (guard205 p guard)
  simpa only [at75, at50, Int.zero_add] using certified
theorem check205 (p : Pattern) : (!walkGuard soko3_2.board support p 75 50 .northEast || decide (bonus 75 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound205 p)
theorem guard206 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 48 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound206 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 48 .northWest = true) : bonus 75 p ≤ bonus 48 p := by
  have certified := compare103 p (guard206 p guard)
  simpa only [at75, at48, Int.zero_add] using certified
theorem check206 (p : Pattern) : (!walkGuard soko3_2.board support p 75 48 .northWest || decide (bonus 75 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound206 p)
theorem guard207 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 102 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound207 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 102 .southEast = true) : bonus 75 p ≤ bonus 102 p := by
  have certified := compare103 p (guard207 p guard)
  simpa only [at75, at102, Int.zero_add] using certified
theorem check207 (p : Pattern) : (!walkGuard soko3_2.board support p 75 102 .southEast || decide (bonus 75 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound207 p)
theorem guard208 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 100 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound208 (p : Pattern) (guard : walkGuard soko3_2.board support p 75 100 .southWest = true) : bonus 75 p ≤ bonus 100 p := by
  have certified := compare103 p (guard208 p guard)
  simpa only [at75, at100, Int.zero_add] using certified
theorem check208 (p : Pattern) : (!walkGuard soko3_2.board support p 75 100 .southWest || decide (bonus 75 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound208 p)
theorem guard209 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 50 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound209 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 50 .north = true) : bonus 76 p ≤ bonus 50 p := by
  have certified := compare103 p (guard209 p guard)
  simpa only [at76, at50, Int.zero_add] using certified
theorem check209 (p : Pattern) : (!walkGuard soko3_2.board support p 76 50 .north || decide (bonus 76 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound209 p)
theorem guard210 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 102 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound210 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 102 .south = true) : bonus 76 p ≤ bonus 102 p := by
  have certified := compare103 p (guard210 p guard)
  simpa only [at76, at102, Int.zero_add] using certified
theorem check210 (p : Pattern) : (!walkGuard soko3_2.board support p 76 102 .south || decide (bonus 76 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound210 p)
theorem guard211 (p : Pattern) (guard : pushGuard support p 76 102 128 128 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound211 (p : Pattern) (guard : pushGuard support p 76 102 128 128 = true) : bonus 76 p ≤ 1 + Generated.soko3_2Potential.boulder 128 - Generated.soko3_2Potential.boulder 102 + bonus 102 (change p 102 (some 128)) := by
  have certified := compare37 p (guard211 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 102 (some 128))
  have normalized := agree0 _ _ (change_representative support p 102 (some 128) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check211 (p : Pattern) : (!pushGuard support p 76 102 128 128 || decide (bonus 76 p ≤ 1 + Generated.soko3_2Potential.boulder 128 - Generated.soko3_2Potential.boulder 102 + bonus 102 (change p 102 (some 128)))) = true :=
  check_of_implication _ _ (bound211 p)
theorem guard212 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 75 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound212 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 75 .west = true) : bonus 76 p ≤ bonus 75 p := by
  have certified := compare103 p (guard212 p guard)
  simpa only [at76, at75, Int.zero_add] using certified
theorem check212 (p : Pattern) : (!walkGuard soko3_2.board support p 76 75 .west || decide (bonus 76 p ≤ bonus 75 p)) = true :=
  check_of_implication _ _ (bound212 p)
theorem guard213 (p : Pattern) (guard : pushGuard support p 76 75 74 74 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound213 (p : Pattern) (guard : pushGuard support p 76 75 74 74 = true) : bonus 76 p ≤ 1 + Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some 74)) := by
  have certified := compare37 p (guard213 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 75 (some 74))
  have normalized := agree0 _ _ (change_representative support p 75 (some 74) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check213 (p : Pattern) : (!pushGuard support p 76 75 74 74 || decide (bonus 76 p ≤ 1 + Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some 74)))) = true :=
  check_of_implication _ _ (bound213 p)
theorem guard214 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 49 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound214 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 49 .northWest = true) : bonus 76 p ≤ bonus 49 p := by
  have certified := compare103 p (guard214 p guard)
  simpa only [at76, at49, Int.zero_add] using certified
theorem check214 (p : Pattern) : (!walkGuard soko3_2.board support p 76 49 .northWest || decide (bonus 76 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound214 p)
theorem guard215 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 101 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound215 (p : Pattern) (guard : walkGuard soko3_2.board support p 76 101 .southWest = true) : bonus 76 p ≤ bonus 101 p := by
  have certified := compare103 p (guard215 p guard)
  simpa only [at76, at101, Int.zero_add] using certified
theorem check215 (p : Pattern) : (!walkGuard soko3_2.board support p 76 101 .southWest || decide (bonus 76 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound215 p)
end NetHack.Sokoban32Refined
