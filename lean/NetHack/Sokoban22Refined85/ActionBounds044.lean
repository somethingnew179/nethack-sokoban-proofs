import NetHack.Sokoban22Refined85.ActionBounds043
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1056 (p : Pattern) (guard : pushGuard support p 262 240 218 218 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1056 (p : Pattern) (guard : pushGuard support p 262 240 218 218 = true) : bonus 262 p ≤ 1 + Generated.soko2_2Potential.boulder 218 - Generated.soko2_2Potential.boulder 240 + bonus 240 (change p 240 (some 218)) := by
  have certified := compare1087 p (guard1056 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 240 (some 218))
  have normalized := agree0 _ _ (change_representative support p 240 (some 218) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1056 (p : Pattern) : (!pushGuard support p 262 240 218 218 || decide (bonus 262 p ≤ 1 + Generated.soko2_2Potential.boulder 218 - Generated.soko2_2Potential.boulder 240 + bonus 240 (change p 240 (some 218)))) = true :=
  check_of_implication _ _ (bound1056 p)
end NetHack.Sokoban22Refined85
