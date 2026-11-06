import NetHack.Sokoban22Refined85.ActionBounds010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard264 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 102 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound264 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 102 .east = true) : bonus 101 p ≤ bonus 102 p := by
  have certified := compare1086 p (guard264 p guard)
  simpa only [at101, at102, Int.zero_add] using certified
theorem check264 (p : Pattern) : (!walkGuard soko2_2.board support p 101 102 .east || decide (bonus 101 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound264 p)
theorem guard265 (p : Pattern) (guard : pushGuard support p 101 102 103 103 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound265 (p : Pattern) (guard : pushGuard support p 101 102 103 103 = true) : bonus 101 p ≤ 1 + Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some 103)) := by
  have certified := compare1087 p (guard265 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 102 (some 103))
  have normalized := agree0 _ _ (change_representative support p 102 (some 103) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check265 (p : Pattern) : (!pushGuard support p 101 102 103 103 || decide (bonus 101 p ≤ 1 + Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some 103)))) = true :=
  check_of_implication _ _ (bound265 p)
theorem guard266 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 100 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound266 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 100 .west = true) : bonus 101 p ≤ bonus 100 p := by
  have certified := compare1086 p (guard266 p guard)
  simpa only [at101, at100, Int.zero_add] using certified
theorem check266 (p : Pattern) : (!walkGuard soko2_2.board support p 101 100 .west || decide (bonus 101 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound266 p)
theorem guard267 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 80 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound267 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 80 .northEast = true) : bonus 101 p ≤ bonus 80 p := by
  have certified := compare1086 p (guard267 p guard)
  simpa only [at101, at80, Int.zero_add] using certified
theorem check267 (p : Pattern) : (!walkGuard soko2_2.board support p 101 80 .northEast || decide (bonus 101 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound267 p)
theorem guard268 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 78 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound268 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 78 .northWest = true) : bonus 101 p ≤ bonus 78 p := by
  have certified := compare1086 p (guard268 p guard)
  simpa only [at101, at78, Int.zero_add] using certified
theorem check268 (p : Pattern) : (!walkGuard soko2_2.board support p 101 78 .northWest || decide (bonus 101 p ≤ bonus 78 p)) = true :=
  check_of_implication _ _ (bound268 p)
theorem guard269 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 124 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound269 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 124 .southEast = true) : bonus 101 p ≤ bonus 124 p := by
  have certified := compare1086 p (guard269 p guard)
  simpa only [at101, at124, Int.zero_add] using certified
theorem check269 (p : Pattern) : (!walkGuard soko2_2.board support p 101 124 .southEast || decide (bonus 101 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound269 p)
theorem guard270 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 122 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound270 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 122 .southWest = true) : bonus 101 p ≤ bonus 122 p := by
  have certified := compare1086 p (guard270 p guard)
  simpa only [at101, at122, Int.zero_add] using certified
theorem check270 (p : Pattern) : (!walkGuard soko2_2.board support p 101 122 .southWest || decide (bonus 101 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound270 p)
theorem guard271 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 80 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound271 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 80 .north = true) : bonus 102 p ≤ bonus 80 p := by
  have certified := compare1086 p (guard271 p guard)
  simpa only [at102, at80, Int.zero_add] using certified
theorem check271 (p : Pattern) : (!walkGuard soko2_2.board support p 102 80 .north || decide (bonus 102 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound271 p)
theorem guard272 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 124 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound272 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 124 .south = true) : bonus 102 p ≤ bonus 124 p := by
  have certified := compare1086 p (guard272 p guard)
  simpa only [at102, at124, Int.zero_add] using certified
theorem check272 (p : Pattern) : (!walkGuard soko2_2.board support p 102 124 .south || decide (bonus 102 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound272 p)
theorem guard273 (p : Pattern) (guard : pushGuard support p 102 124 146 146 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound273 (p : Pattern) (guard : pushGuard support p 102 124 146 146 = true) : bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some 146)) := by
  have certified := compare1087 p (guard273 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 124 (some 146))
  have normalized := agree0 _ _ (change_representative support p 124 (some 146) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check273 (p : Pattern) : (!pushGuard support p 102 124 146 146 || decide (bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some 146)))) = true :=
  check_of_implication _ _ (bound273 p)
theorem guard274 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 103 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound274 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 103 .east = true) : bonus 102 p ≤ bonus 103 p := by
  have certified := compare1086 p (guard274 p guard)
  simpa only [at102, at103, Int.zero_add] using certified
theorem check274 (p : Pattern) : (!walkGuard soko2_2.board support p 102 103 .east || decide (bonus 102 p ≤ bonus 103 p)) = true :=
  check_of_implication _ _ (bound274 p)
theorem guard275 (p : Pattern) (guard : pushGuard support p 102 103 104 104 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound275 (p : Pattern) (guard : pushGuard support p 102 103 104 104 = true) : bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some 104)) := by
  have certified := compare1087 p (guard275 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 103 (some 104))
  have normalized := agree0 _ _ (change_representative support p 103 (some 104) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check275 (p : Pattern) : (!pushGuard support p 102 103 104 104 || decide (bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some 104)))) = true :=
  check_of_implication _ _ (bound275 p)
theorem guard276 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 101 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound276 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 101 .west = true) : bonus 102 p ≤ bonus 101 p := by
  have certified := compare1086 p (guard276 p guard)
  simpa only [at102, at101, Int.zero_add] using certified
theorem check276 (p : Pattern) : (!walkGuard soko2_2.board support p 102 101 .west || decide (bonus 102 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound276 p)
theorem guard277 (p : Pattern) (guard : pushGuard support p 102 101 100 100 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound277 (p : Pattern) (guard : pushGuard support p 102 101 100 100 = true) : bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder 100 - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some 100)) := by
  have certified := compare1087 p (guard277 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 101 (some 100))
  have normalized := agree0 _ _ (change_representative support p 101 (some 100) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check277 (p : Pattern) : (!pushGuard support p 102 101 100 100 || decide (bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder 100 - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some 100)))) = true :=
  check_of_implication _ _ (bound277 p)
theorem guard278 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 81 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound278 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 81 .northEast = true) : bonus 102 p ≤ bonus 81 p := by
  have certified := compare1086 p (guard278 p guard)
  simpa only [at102, at81, Int.zero_add] using certified
theorem check278 (p : Pattern) : (!walkGuard soko2_2.board support p 102 81 .northEast || decide (bonus 102 p ≤ bonus 81 p)) = true :=
  check_of_implication _ _ (bound278 p)
theorem guard279 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 79 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound279 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 79 .northWest = true) : bonus 102 p ≤ bonus 79 p := by
  have certified := compare1086 p (guard279 p guard)
  simpa only [at102, at79, Int.zero_add] using certified
theorem check279 (p : Pattern) : (!walkGuard soko2_2.board support p 102 79 .northWest || decide (bonus 102 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound279 p)
theorem guard280 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 125 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound280 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 125 .southEast = true) : bonus 102 p ≤ bonus 125 p := by
  have certified := compare1086 p (guard280 p guard)
  simpa only [at102, at125, Int.zero_add] using certified
theorem check280 (p : Pattern) : (!walkGuard soko2_2.board support p 102 125 .southEast || decide (bonus 102 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound280 p)
theorem guard281 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 123 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound281 (p : Pattern) (guard : walkGuard soko2_2.board support p 102 123 .southWest = true) : bonus 102 p ≤ bonus 123 p := by
  have certified := compare1086 p (guard281 p guard)
  simpa only [at102, at123, Int.zero_add] using certified
theorem check281 (p : Pattern) : (!walkGuard soko2_2.board support p 102 123 .southWest || decide (bonus 102 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound281 p)
theorem guard282 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 81 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound282 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 81 .north = true) : bonus 103 p ≤ bonus 81 p := by
  have certified := compare1086 p (guard282 p guard)
  simpa only [at103, at81, Int.zero_add] using certified
theorem check282 (p : Pattern) : (!walkGuard soko2_2.board support p 103 81 .north || decide (bonus 103 p ≤ bonus 81 p)) = true :=
  check_of_implication _ _ (bound282 p)
theorem guard283 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 125 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound283 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 125 .south = true) : bonus 103 p ≤ bonus 125 p := by
  have certified := compare1086 p (guard283 p guard)
  simpa only [at103, at125, Int.zero_add] using certified
theorem check283 (p : Pattern) : (!walkGuard soko2_2.board support p 103 125 .south || decide (bonus 103 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound283 p)
theorem guard284 (p : Pattern) (guard : pushGuard support p 103 125 147 147 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound284 (p : Pattern) (guard : pushGuard support p 103 125 147 147 = true) : bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some 147)) := by
  have certified := compare1087 p (guard284 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 125 (some 147))
  have normalized := agree0 _ _ (change_representative support p 125 (some 147) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check284 (p : Pattern) : (!pushGuard support p 103 125 147 147 || decide (bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some 147)))) = true :=
  check_of_implication _ _ (bound284 p)
theorem guard285 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 104 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound285 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 104 .east = true) : bonus 103 p ≤ bonus 104 p := by
  have certified := compare1086 p (guard285 p guard)
  simpa only [at103, at104, Int.zero_add] using certified
theorem check285 (p : Pattern) : (!walkGuard soko2_2.board support p 103 104 .east || decide (bonus 103 p ≤ bonus 104 p)) = true :=
  check_of_implication _ _ (bound285 p)
theorem guard286 (p : Pattern) (guard : pushGuard support p 103 104 105 105 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound286 (p : Pattern) (guard : pushGuard support p 103 104 105 105 = true) : bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder 105 - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some 105)) := by
  have certified := compare1087 p (guard286 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 104 (some 105))
  have normalized := agree0 _ _ (change_representative support p 104 (some 105) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check286 (p : Pattern) : (!pushGuard support p 103 104 105 105 || decide (bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder 105 - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some 105)))) = true :=
  check_of_implication _ _ (bound286 p)
theorem guard287 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 102 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound287 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 102 .west = true) : bonus 103 p ≤ bonus 102 p := by
  have certified := compare1086 p (guard287 p guard)
  simpa only [at103, at102, Int.zero_add] using certified
theorem check287 (p : Pattern) : (!walkGuard soko2_2.board support p 103 102 .west || decide (bonus 103 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound287 p)
end NetHack.Sokoban22Refined85
