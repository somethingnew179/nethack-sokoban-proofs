import NetHack.Sokoban32Refined.ActionBounds055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1344 (p : Pattern) (guard : walkGuard soko3_2.board support p 321 295 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1344 (p : Pattern) (guard : walkGuard soko3_2.board support p 321 295 .north = true) : bonus 321 p ≤ bonus 295 p := by
  have certified := compare0 p (guard1344 p guard)
  simpa only [at321, at295, Int.zero_add] using certified
theorem check1344 (p : Pattern) : (!walkGuard soko3_2.board support p 321 295 .north || decide (bonus 321 p ≤ bonus 295 p)) = true :=
  check_of_implication _ _ (bound1344 p)
theorem guard1345 (p : Pattern) (guard : pushGuard support p 321 295 269 269 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1345 (p : Pattern) (guard : pushGuard support p 321 295 269 269 = true) : bonus 321 p ≤ 1 + Generated.soko3_2Potential.boulder 269 - Generated.soko3_2Potential.boulder 295 + bonus 295 (change p 295 (some 269)) := by
  have certified := compare0 p (guard1345 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 295 (some 269))
  have normalized := agree134 _ _ (change_representative support p 295 (some 269) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1345 (p : Pattern) : (!pushGuard support p 321 295 269 269 || decide (bonus 321 p ≤ 1 + Generated.soko3_2Potential.boulder 269 - Generated.soko3_2Potential.boulder 295 + bonus 295 (change p 295 (some 269)))) = true :=
  check_of_implication _ _ (bound1345 p)
theorem guard1346 (p : Pattern) (guard : walkGuard soko3_2.board support p 321 320 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1346 (p : Pattern) (guard : walkGuard soko3_2.board support p 321 320 .west = true) : bonus 321 p ≤ bonus 320 p := by
  have certified := compare0 p (guard1346 p guard)
  simpa only [at321, at320, Int.zero_add] using certified
theorem check1346 (p : Pattern) : (!walkGuard soko3_2.board support p 321 320 .west || decide (bonus 321 p ≤ bonus 320 p)) = true :=
  check_of_implication _ _ (bound1346 p)
theorem guard1347 (p : Pattern) (guard : walkGuard soko3_2.board support p 321 294 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1347 (p : Pattern) (guard : walkGuard soko3_2.board support p 321 294 .northWest = true) : bonus 321 p ≤ bonus 294 p := by
  have certified := compare0 p (guard1347 p guard)
  simpa only [at321, at294, Int.zero_add] using certified
theorem check1347 (p : Pattern) : (!walkGuard soko3_2.board support p 321 294 .northWest || decide (bonus 321 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound1347 p)
end NetHack.Sokoban32Refined
