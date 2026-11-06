import NetHack.Sokoban22Refined85.ActionBounds011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard288 (p : Pattern) (guard : pushGuard support p 103 102 101 101 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound288 (p : Pattern) (guard : pushGuard support p 103 102 101 101 = true) : bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder 101 - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some 101)) := by
  have certified := compare1087 p (guard288 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 102 (some 101))
  have normalized := agree0 _ _ (change_representative support p 102 (some 101) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check288 (p : Pattern) : (!pushGuard support p 103 102 101 101 || decide (bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder 101 - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some 101)))) = true :=
  check_of_implication _ _ (bound288 p)
theorem guard289 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 82 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound289 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 82 .northEast = true) : bonus 103 p ≤ bonus 82 p := by
  have certified := compare1086 p (guard289 p guard)
  simpa only [at103, at82, Int.zero_add] using certified
theorem check289 (p : Pattern) : (!walkGuard soko2_2.board support p 103 82 .northEast || decide (bonus 103 p ≤ bonus 82 p)) = true :=
  check_of_implication _ _ (bound289 p)
theorem guard290 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 80 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound290 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 80 .northWest = true) : bonus 103 p ≤ bonus 80 p := by
  have certified := compare1086 p (guard290 p guard)
  simpa only [at103, at80, Int.zero_add] using certified
theorem check290 (p : Pattern) : (!walkGuard soko2_2.board support p 103 80 .northWest || decide (bonus 103 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound290 p)
theorem guard291 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 126 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound291 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 126 .southEast = true) : bonus 103 p ≤ bonus 126 p := by
  have certified := compare1086 p (guard291 p guard)
  simpa only [at103, at126, Int.zero_add] using certified
theorem check291 (p : Pattern) : (!walkGuard soko2_2.board support p 103 126 .southEast || decide (bonus 103 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound291 p)
theorem guard292 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 124 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound292 (p : Pattern) (guard : walkGuard soko2_2.board support p 103 124 .southWest = true) : bonus 103 p ≤ bonus 124 p := by
  have certified := compare1086 p (guard292 p guard)
  simpa only [at103, at124, Int.zero_add] using certified
theorem check292 (p : Pattern) : (!walkGuard soko2_2.board support p 103 124 .southWest || decide (bonus 103 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound292 p)
theorem guard293 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 82 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound293 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 82 .north = true) : bonus 104 p ≤ bonus 82 p := by
  have certified := compare1086 p (guard293 p guard)
  simpa only [at104, at82, Int.zero_add] using certified
theorem check293 (p : Pattern) : (!walkGuard soko2_2.board support p 104 82 .north || decide (bonus 104 p ≤ bonus 82 p)) = true :=
  check_of_implication _ _ (bound293 p)
theorem guard294 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 126 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound294 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 126 .south = true) : bonus 104 p ≤ bonus 126 p := by
  have certified := compare1086 p (guard294 p guard)
  simpa only [at104, at126, Int.zero_add] using certified
theorem check294 (p : Pattern) : (!walkGuard soko2_2.board support p 104 126 .south || decide (bonus 104 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound294 p)
theorem guard295 (p : Pattern) (guard : pushGuard support p 104 126 148 148 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound295 (p : Pattern) (guard : pushGuard support p 104 126 148 148 = true) : bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some 148)) := by
  have certified := compare1087 p (guard295 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 126 (some 148))
  have normalized := agree0 _ _ (change_representative support p 126 (some 148) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check295 (p : Pattern) : (!pushGuard support p 104 126 148 148 || decide (bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some 148)))) = true :=
  check_of_implication _ _ (bound295 p)
theorem guard296 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 105 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound296 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 105 .east = true) : bonus 104 p ≤ bonus 105 p := by
  have certified := compare1086 p (guard296 p guard)
  simpa only [at104, at105, Int.zero_add] using certified
theorem check296 (p : Pattern) : (!walkGuard soko2_2.board support p 104 105 .east || decide (bonus 104 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound296 p)
theorem guard297 (p : Pattern) (guard : pushGuard support p 104 105 106 106 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound297 (p : Pattern) (guard : pushGuard support p 104 105 106 106 = true) : bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder 106 - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some 106)) := by
  have certified := compare1087 p (guard297 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 105 (some 106))
  have normalized := agree0 _ _ (change_representative support p 105 (some 106) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check297 (p : Pattern) : (!pushGuard support p 104 105 106 106 || decide (bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder 106 - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some 106)))) = true :=
  check_of_implication _ _ (bound297 p)
theorem guard298 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 103 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound298 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 103 .west = true) : bonus 104 p ≤ bonus 103 p := by
  have certified := compare1086 p (guard298 p guard)
  simpa only [at104, at103, Int.zero_add] using certified
theorem check298 (p : Pattern) : (!walkGuard soko2_2.board support p 104 103 .west || decide (bonus 104 p ≤ bonus 103 p)) = true :=
  check_of_implication _ _ (bound298 p)
theorem guard299 (p : Pattern) (guard : pushGuard support p 104 103 102 102 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound299 (p : Pattern) (guard : pushGuard support p 104 103 102 102 = true) : bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some 102)) := by
  have certified := compare1087 p (guard299 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 103 (some 102))
  have normalized := agree0 _ _ (change_representative support p 103 (some 102) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check299 (p : Pattern) : (!pushGuard support p 104 103 102 102 || decide (bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some 102)))) = true :=
  check_of_implication _ _ (bound299 p)
theorem guard300 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 83 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound300 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 83 .northEast = true) : bonus 104 p ≤ bonus 83 p := by
  have certified := compare1086 p (guard300 p guard)
  simpa only [at104, at83, Int.zero_add] using certified
theorem check300 (p : Pattern) : (!walkGuard soko2_2.board support p 104 83 .northEast || decide (bonus 104 p ≤ bonus 83 p)) = true :=
  check_of_implication _ _ (bound300 p)
theorem guard301 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 81 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound301 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 81 .northWest = true) : bonus 104 p ≤ bonus 81 p := by
  have certified := compare1086 p (guard301 p guard)
  simpa only [at104, at81, Int.zero_add] using certified
theorem check301 (p : Pattern) : (!walkGuard soko2_2.board support p 104 81 .northWest || decide (bonus 104 p ≤ bonus 81 p)) = true :=
  check_of_implication _ _ (bound301 p)
theorem guard302 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 127 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound302 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 127 .southEast = true) : bonus 104 p ≤ bonus 127 p := by
  have certified := compare1086 p (guard302 p guard)
  simpa only [at104, at127, Int.zero_add] using certified
theorem check302 (p : Pattern) : (!walkGuard soko2_2.board support p 104 127 .southEast || decide (bonus 104 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound302 p)
theorem guard303 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 125 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound303 (p : Pattern) (guard : walkGuard soko2_2.board support p 104 125 .southWest = true) : bonus 104 p ≤ bonus 125 p := by
  have certified := compare1086 p (guard303 p guard)
  simpa only [at104, at125, Int.zero_add] using certified
theorem check303 (p : Pattern) : (!walkGuard soko2_2.board support p 104 125 .southWest || decide (bonus 104 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound303 p)
theorem guard304 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 83 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound304 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 83 .north = true) : bonus 105 p ≤ bonus 83 p := by
  have certified := compare1086 p (guard304 p guard)
  simpa only [at105, at83, Int.zero_add] using certified
theorem check304 (p : Pattern) : (!walkGuard soko2_2.board support p 105 83 .north || decide (bonus 105 p ≤ bonus 83 p)) = true :=
  check_of_implication _ _ (bound304 p)
theorem guard305 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 127 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound305 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 127 .south = true) : bonus 105 p ≤ bonus 127 p := by
  have certified := compare1086 p (guard305 p guard)
  simpa only [at105, at127, Int.zero_add] using certified
theorem check305 (p : Pattern) : (!walkGuard soko2_2.board support p 105 127 .south || decide (bonus 105 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound305 p)
theorem guard306 (p : Pattern) (guard : pushGuard support p 105 127 149 149 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound306 (p : Pattern) (guard : pushGuard support p 105 127 149 149 = true) : bonus 105 p ≤ 1 + Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some 149)) := by
  have certified := compare1087 p (guard306 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 127 (some 149))
  have normalized := agree0 _ _ (change_representative support p 127 (some 149) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check306 (p : Pattern) : (!pushGuard support p 105 127 149 149 || decide (bonus 105 p ≤ 1 + Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some 149)))) = true :=
  check_of_implication _ _ (bound306 p)
theorem guard307 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 106 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound307 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 106 .east = true) : bonus 105 p ≤ bonus 106 p := by
  have certified := compare1086 p (guard307 p guard)
  simpa only [at105, at106, Int.zero_add] using certified
theorem check307 (p : Pattern) : (!walkGuard soko2_2.board support p 105 106 .east || decide (bonus 105 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound307 p)
theorem guard308 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 104 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound308 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 104 .west = true) : bonus 105 p ≤ bonus 104 p := by
  have certified := compare1086 p (guard308 p guard)
  simpa only [at105, at104, Int.zero_add] using certified
theorem check308 (p : Pattern) : (!walkGuard soko2_2.board support p 105 104 .west || decide (bonus 105 p ≤ bonus 104 p)) = true :=
  check_of_implication _ _ (bound308 p)
theorem guard309 (p : Pattern) (guard : pushGuard support p 105 104 103 103 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound309 (p : Pattern) (guard : pushGuard support p 105 104 103 103 = true) : bonus 105 p ≤ 1 + Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some 103)) := by
  have certified := compare1087 p (guard309 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 104 (some 103))
  have normalized := agree0 _ _ (change_representative support p 104 (some 103) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check309 (p : Pattern) : (!pushGuard support p 105 104 103 103 || decide (bonus 105 p ≤ 1 + Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some 103)))) = true :=
  check_of_implication _ _ (bound309 p)
theorem guard310 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 84 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound310 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 84 .northEast = true) : bonus 105 p ≤ bonus 84 p := by
  have certified := compare1086 p (guard310 p guard)
  simpa only [at105, at84, Int.zero_add] using certified
theorem check310 (p : Pattern) : (!walkGuard soko2_2.board support p 105 84 .northEast || decide (bonus 105 p ≤ bonus 84 p)) = true :=
  check_of_implication _ _ (bound310 p)
theorem guard311 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 82 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound311 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 82 .northWest = true) : bonus 105 p ≤ bonus 82 p := by
  have certified := compare1086 p (guard311 p guard)
  simpa only [at105, at82, Int.zero_add] using certified
theorem check311 (p : Pattern) : (!walkGuard soko2_2.board support p 105 82 .northWest || decide (bonus 105 p ≤ bonus 82 p)) = true :=
  check_of_implication _ _ (bound311 p)
end NetHack.Sokoban22Refined85
