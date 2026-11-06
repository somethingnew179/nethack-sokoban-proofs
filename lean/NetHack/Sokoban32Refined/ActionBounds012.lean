import NetHack.Sokoban32Refined.ActionBounds011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard288 (p : Pattern) (guard : pushGuard support p 98 99 100 100 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound288 (p : Pattern) (guard : pushGuard support p 98 99 100 100 = true) : bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some 100)) := by
  have certified := compare37 p (guard288 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 99 (some 100))
  have normalized := agree0 _ _ (change_representative support p 99 (some 100) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check288 (p : Pattern) : (!pushGuard support p 98 99 100 100 || decide (bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some 100)))) = true :=
  check_of_implication _ _ (bound288 p)
theorem guard289 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 97 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound289 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 97 .west = true) : bonus 98 p ≤ bonus 97 p := by
  have certified := compare103 p (guard289 p guard)
  simpa only [at98, at97, Int.zero_add] using certified
theorem check289 (p : Pattern) : (!walkGuard soko3_2.board support p 98 97 .west || decide (bonus 98 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound289 p)
theorem guard290 (p : Pattern) (guard : pushGuard support p 98 97 96 96 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound290 (p : Pattern) (guard : pushGuard support p 98 97 96 96 = true) : bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some 96)) := by
  have certified := compare37 p (guard290 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 97 (some 96))
  have normalized := agree0 _ _ (change_representative support p 97 (some 96) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check290 (p : Pattern) : (!pushGuard support p 98 97 96 96 || decide (bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some 96)))) = true :=
  check_of_implication _ _ (bound290 p)
theorem guard291 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 73 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound291 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 73 .northEast = true) : bonus 98 p ≤ bonus 73 p := by
  have certified := compare103 p (guard291 p guard)
  simpa only [at98, at73, Int.zero_add] using certified
theorem check291 (p : Pattern) : (!walkGuard soko3_2.board support p 98 73 .northEast || decide (bonus 98 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound291 p)
theorem guard292 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 71 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound292 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 71 .northWest = true) : bonus 98 p ≤ bonus 71 p := by
  have certified := compare103 p (guard292 p guard)
  simpa only [at98, at71, Int.zero_add] using certified
theorem check292 (p : Pattern) : (!walkGuard soko3_2.board support p 98 71 .northWest || decide (bonus 98 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound292 p)
theorem guard293 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 125 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound293 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 125 .southEast = true) : bonus 98 p ≤ bonus 125 p := by
  have certified := compare103 p (guard293 p guard)
  simpa only [at98, at125, Int.zero_add] using certified
theorem check293 (p : Pattern) : (!walkGuard soko3_2.board support p 98 125 .southEast || decide (bonus 98 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound293 p)
theorem guard294 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 123 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound294 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 123 .southWest = true) : bonus 98 p ≤ bonus 123 p := by
  have certified := compare103 p (guard294 p guard)
  simpa only [at98, at123, Int.zero_add] using certified
theorem check294 (p : Pattern) : (!walkGuard soko3_2.board support p 98 123 .southWest || decide (bonus 98 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound294 p)
theorem guard295 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 73 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound295 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 73 .north = true) : bonus 99 p ≤ bonus 73 p := by
  have certified := compare103 p (guard295 p guard)
  simpa only [at99, at73, Int.zero_add] using certified
theorem check295 (p : Pattern) : (!walkGuard soko3_2.board support p 99 73 .north || decide (bonus 99 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound295 p)
theorem guard296 (p : Pattern) (guard : pushGuard support p 99 73 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound296 (p : Pattern) (guard : pushGuard support p 99 73 47 47 = true) : bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder 47 - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some 47)) := by
  have certified := compare37 p (guard296 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 73 (some 47))
  have normalized := agree0 _ _ (change_representative support p 73 (some 47) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check296 (p : Pattern) : (!pushGuard support p 99 73 47 47 || decide (bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder 47 - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some 47)))) = true :=
  check_of_implication _ _ (bound296 p)
theorem guard297 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 125 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound297 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 125 .south = true) : bonus 99 p ≤ bonus 125 p := by
  have certified := compare103 p (guard297 p guard)
  simpa only [at99, at125, Int.zero_add] using certified
theorem check297 (p : Pattern) : (!walkGuard soko3_2.board support p 99 125 .south || decide (bonus 99 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound297 p)
theorem guard298 (p : Pattern) (guard : pushGuard support p 99 125 151 151 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound298 (p : Pattern) (guard : pushGuard support p 99 125 151 151 = true) : bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some 151)) := by
  have certified := compare37 p (guard298 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 125 (some 151))
  have normalized := agree0 _ _ (change_representative support p 125 (some 151) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check298 (p : Pattern) : (!pushGuard support p 99 125 151 151 || decide (bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some 151)))) = true :=
  check_of_implication _ _ (bound298 p)
theorem guard299 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 100 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound299 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 100 .east = true) : bonus 99 p ≤ bonus 100 p := by
  have certified := compare103 p (guard299 p guard)
  simpa only [at99, at100, Int.zero_add] using certified
theorem check299 (p : Pattern) : (!walkGuard soko3_2.board support p 99 100 .east || decide (bonus 99 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound299 p)
theorem guard300 (p : Pattern) (guard : pushGuard support p 99 100 101 101 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound300 (p : Pattern) (guard : pushGuard support p 99 100 101 101 = true) : bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some 101)) := by
  have certified := compare37 p (guard300 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 100 (some 101))
  have normalized := agree0 _ _ (change_representative support p 100 (some 101) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check300 (p : Pattern) : (!pushGuard support p 99 100 101 101 || decide (bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some 101)))) = true :=
  check_of_implication _ _ (bound300 p)
theorem guard301 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 98 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound301 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 98 .west = true) : bonus 99 p ≤ bonus 98 p := by
  have certified := compare103 p (guard301 p guard)
  simpa only [at99, at98, Int.zero_add] using certified
theorem check301 (p : Pattern) : (!walkGuard soko3_2.board support p 99 98 .west || decide (bonus 99 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound301 p)
theorem guard302 (p : Pattern) (guard : pushGuard support p 99 98 97 97 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound302 (p : Pattern) (guard : pushGuard support p 99 98 97 97 = true) : bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some 97)) := by
  have certified := compare37 p (guard302 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 98 (some 97))
  have normalized := agree0 _ _ (change_representative support p 98 (some 97) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check302 (p : Pattern) : (!pushGuard support p 99 98 97 97 || decide (bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some 97)))) = true :=
  check_of_implication _ _ (bound302 p)
theorem guard303 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 74 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound303 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 74 .northEast = true) : bonus 99 p ≤ bonus 74 p := by
  have certified := compare103 p (guard303 p guard)
  simpa only [at99, at74, Int.zero_add] using certified
theorem check303 (p : Pattern) : (!walkGuard soko3_2.board support p 99 74 .northEast || decide (bonus 99 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound303 p)
theorem guard304 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 72 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound304 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 72 .northWest = true) : bonus 99 p ≤ bonus 72 p := by
  have certified := compare103 p (guard304 p guard)
  simpa only [at99, at72, Int.zero_add] using certified
theorem check304 (p : Pattern) : (!walkGuard soko3_2.board support p 99 72 .northWest || decide (bonus 99 p ≤ bonus 72 p)) = true :=
  check_of_implication _ _ (bound304 p)
theorem guard305 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 126 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound305 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 126 .southEast = true) : bonus 99 p ≤ bonus 126 p := by
  have certified := compare103 p (guard305 p guard)
  simpa only [at99, at126, Int.zero_add] using certified
theorem check305 (p : Pattern) : (!walkGuard soko3_2.board support p 99 126 .southEast || decide (bonus 99 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound305 p)
theorem guard306 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 124 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound306 (p : Pattern) (guard : walkGuard soko3_2.board support p 99 124 .southWest = true) : bonus 99 p ≤ bonus 124 p := by
  have certified := compare103 p (guard306 p guard)
  simpa only [at99, at124, Int.zero_add] using certified
theorem check306 (p : Pattern) : (!walkGuard soko3_2.board support p 99 124 .southWest || decide (bonus 99 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound306 p)
theorem guard307 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 74 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound307 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 74 .north = true) : bonus 100 p ≤ bonus 74 p := by
  have certified := compare103 p (guard307 p guard)
  simpa only [at100, at74, Int.zero_add] using certified
theorem check307 (p : Pattern) : (!walkGuard soko3_2.board support p 100 74 .north || decide (bonus 100 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound307 p)
theorem guard308 (p : Pattern) (guard : pushGuard support p 100 74 48 48 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound308 (p : Pattern) (guard : pushGuard support p 100 74 48 48 = true) : bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder 48 - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some 48)) := by
  have certified := compare37 p (guard308 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 74 (some 48))
  have normalized := agree0 _ _ (change_representative support p 74 (some 48) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check308 (p : Pattern) : (!pushGuard support p 100 74 48 48 || decide (bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder 48 - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some 48)))) = true :=
  check_of_implication _ _ (bound308 p)
theorem guard309 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 126 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound309 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 126 .south = true) : bonus 100 p ≤ bonus 126 p := by
  have certified := compare103 p (guard309 p guard)
  simpa only [at100, at126, Int.zero_add] using certified
theorem check309 (p : Pattern) : (!walkGuard soko3_2.board support p 100 126 .south || decide (bonus 100 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound309 p)
theorem guard310 (p : Pattern) (guard : pushGuard support p 100 126 152 152 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound310 (p : Pattern) (guard : pushGuard support p 100 126 152 152 = true) : bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some 152)) := by
  have certified := compare37 p (guard310 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 126 (some 152))
  have normalized := agree0 _ _ (change_representative support p 126 (some 152) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check310 (p : Pattern) : (!pushGuard support p 100 126 152 152 || decide (bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some 152)))) = true :=
  check_of_implication _ _ (bound310 p)
theorem guard311 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 101 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound311 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 101 .east = true) : bonus 100 p ≤ bonus 101 p := by
  have certified := compare103 p (guard311 p guard)
  simpa only [at100, at101, Int.zero_add] using certified
theorem check311 (p : Pattern) : (!walkGuard soko3_2.board support p 100 101 .east || decide (bonus 100 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound311 p)
end NetHack.Sokoban32Refined
