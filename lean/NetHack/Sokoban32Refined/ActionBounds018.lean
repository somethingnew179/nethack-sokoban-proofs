import NetHack.Sokoban32Refined.ActionBounds017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard432 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 148 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound432 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 148 .southWest = true) : bonus 123 p ≤ bonus 148 p := by
  have certified := compare103 p (guard432 p guard)
  simpa only [at123, at148, Int.zero_add] using certified
theorem check432 (p : Pattern) : (!walkGuard soko3_2.board support p 123 148 .southWest || decide (bonus 123 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound432 p)
theorem guard433 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 98 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound433 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 98 .north = true) : bonus 124 p ≤ bonus 98 p := by
  have certified := compare103 p (guard433 p guard)
  simpa only [at124, at98, Int.zero_add] using certified
theorem check433 (p : Pattern) : (!walkGuard soko3_2.board support p 124 98 .north || decide (bonus 124 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound433 p)
theorem guard434 (p : Pattern) (guard : pushGuard support p 124 98 72 72 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound434 (p : Pattern) (guard : pushGuard support p 124 98 72 72 = true) : bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some 72)) := by
  have certified := compare37 p (guard434 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 98 (some 72))
  have normalized := agree0 _ _ (change_representative support p 98 (some 72) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check434 (p : Pattern) : (!pushGuard support p 124 98 72 72 || decide (bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some 72)))) = true :=
  check_of_implication _ _ (bound434 p)
theorem guard435 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 150 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound435 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 150 .south = true) : bonus 124 p ≤ bonus 150 p := by
  have certified := compare103 p (guard435 p guard)
  simpa only [at124, at150, Int.zero_add] using certified
theorem check435 (p : Pattern) : (!walkGuard soko3_2.board support p 124 150 .south || decide (bonus 124 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound435 p)
theorem guard436 (p : Pattern) (guard : pushGuard support p 124 150 176 176 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound436 (p : Pattern) (guard : pushGuard support p 124 150 176 176 = true) : bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some 176)) := by
  have certified := compare37 p (guard436 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 150 (some 176))
  have normalized := agree0 _ _ (change_representative support p 150 (some 176) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check436 (p : Pattern) : (!pushGuard support p 124 150 176 176 || decide (bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some 176)))) = true :=
  check_of_implication _ _ (bound436 p)
theorem guard437 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 125 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound437 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 125 .east = true) : bonus 124 p ≤ bonus 125 p := by
  have certified := compare103 p (guard437 p guard)
  simpa only [at124, at125, Int.zero_add] using certified
theorem check437 (p : Pattern) : (!walkGuard soko3_2.board support p 124 125 .east || decide (bonus 124 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound437 p)
theorem guard438 (p : Pattern) (guard : pushGuard support p 124 125 126 126 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound438 (p : Pattern) (guard : pushGuard support p 124 125 126 126 = true) : bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some 126)) := by
  have certified := compare37 p (guard438 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 125 (some 126))
  have normalized := agree0 _ _ (change_representative support p 125 (some 126) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check438 (p : Pattern) : (!pushGuard support p 124 125 126 126 || decide (bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some 126)))) = true :=
  check_of_implication _ _ (bound438 p)
theorem guard439 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 123 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound439 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 123 .west = true) : bonus 124 p ≤ bonus 123 p := by
  have certified := compare103 p (guard439 p guard)
  simpa only [at124, at123, Int.zero_add] using certified
theorem check439 (p : Pattern) : (!walkGuard soko3_2.board support p 124 123 .west || decide (bonus 124 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound439 p)
theorem guard440 (p : Pattern) (guard : pushGuard support p 124 123 122 122 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound440 (p : Pattern) (guard : pushGuard support p 124 123 122 122 = true) : bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some 122)) := by
  have certified := compare37 p (guard440 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 123 (some 122))
  have normalized := agree0 _ _ (change_representative support p 123 (some 122) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check440 (p : Pattern) : (!pushGuard support p 124 123 122 122 || decide (bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some 122)))) = true :=
  check_of_implication _ _ (bound440 p)
theorem guard441 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 99 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound441 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 99 .northEast = true) : bonus 124 p ≤ bonus 99 p := by
  have certified := compare103 p (guard441 p guard)
  simpa only [at124, at99, Int.zero_add] using certified
theorem check441 (p : Pattern) : (!walkGuard soko3_2.board support p 124 99 .northEast || decide (bonus 124 p ≤ bonus 99 p)) = true :=
  check_of_implication _ _ (bound441 p)
theorem guard442 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 97 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound442 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 97 .northWest = true) : bonus 124 p ≤ bonus 97 p := by
  have certified := compare103 p (guard442 p guard)
  simpa only [at124, at97, Int.zero_add] using certified
theorem check442 (p : Pattern) : (!walkGuard soko3_2.board support p 124 97 .northWest || decide (bonus 124 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound442 p)
theorem guard443 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 151 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound443 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 151 .southEast = true) : bonus 124 p ≤ bonus 151 p := by
  have certified := compare103 p (guard443 p guard)
  simpa only [at124, at151, Int.zero_add] using certified
theorem check443 (p : Pattern) : (!walkGuard soko3_2.board support p 124 151 .southEast || decide (bonus 124 p ≤ bonus 151 p)) = true :=
  check_of_implication _ _ (bound443 p)
theorem guard444 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 149 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound444 (p : Pattern) (guard : walkGuard soko3_2.board support p 124 149 .southWest = true) : bonus 124 p ≤ bonus 149 p := by
  have certified := compare103 p (guard444 p guard)
  simpa only [at124, at149, Int.zero_add] using certified
theorem check444 (p : Pattern) : (!walkGuard soko3_2.board support p 124 149 .southWest || decide (bonus 124 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound444 p)
theorem guard445 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 99 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound445 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 99 .north = true) : bonus 125 p ≤ bonus 99 p := by
  have certified := compare103 p (guard445 p guard)
  simpa only [at125, at99, Int.zero_add] using certified
theorem check445 (p : Pattern) : (!walkGuard soko3_2.board support p 125 99 .north || decide (bonus 125 p ≤ bonus 99 p)) = true :=
  check_of_implication _ _ (bound445 p)
theorem guard446 (p : Pattern) (guard : pushGuard support p 125 99 73 73 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound446 (p : Pattern) (guard : pushGuard support p 125 99 73 73 = true) : bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some 73)) := by
  have certified := compare37 p (guard446 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 99 (some 73))
  have normalized := agree0 _ _ (change_representative support p 99 (some 73) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check446 (p : Pattern) : (!pushGuard support p 125 99 73 73 || decide (bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some 73)))) = true :=
  check_of_implication _ _ (bound446 p)
theorem guard447 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 151 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound447 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 151 .south = true) : bonus 125 p ≤ bonus 151 p := by
  have certified := compare103 p (guard447 p guard)
  simpa only [at125, at151, Int.zero_add] using certified
theorem check447 (p : Pattern) : (!walkGuard soko3_2.board support p 125 151 .south || decide (bonus 125 p ≤ bonus 151 p)) = true :=
  check_of_implication _ _ (bound447 p)
theorem guard448 (p : Pattern) (guard : pushGuard support p 125 151 177 177 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound448 (p : Pattern) (guard : pushGuard support p 125 151 177 177 = true) : bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some 177)) := by
  have certified := compare37 p (guard448 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 151 (some 177))
  have normalized := agree0 _ _ (change_representative support p 151 (some 177) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check448 (p : Pattern) : (!pushGuard support p 125 151 177 177 || decide (bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some 177)))) = true :=
  check_of_implication _ _ (bound448 p)
theorem guard449 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 126 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound449 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 126 .east = true) : bonus 125 p ≤ bonus 126 p := by
  have certified := compare103 p (guard449 p guard)
  simpa only [at125, at126, Int.zero_add] using certified
theorem check449 (p : Pattern) : (!walkGuard soko3_2.board support p 125 126 .east || decide (bonus 125 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound449 p)
theorem guard450 (p : Pattern) (guard : pushGuard support p 125 126 127 127 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound450 (p : Pattern) (guard : pushGuard support p 125 126 127 127 = true) : bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some 127)) := by
  have certified := compare37 p (guard450 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 126 (some 127))
  have normalized := agree0 _ _ (change_representative support p 126 (some 127) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check450 (p : Pattern) : (!pushGuard support p 125 126 127 127 || decide (bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some 127)))) = true :=
  check_of_implication _ _ (bound450 p)
theorem guard451 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 124 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound451 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 124 .west = true) : bonus 125 p ≤ bonus 124 p := by
  have certified := compare103 p (guard451 p guard)
  simpa only [at125, at124, Int.zero_add] using certified
theorem check451 (p : Pattern) : (!walkGuard soko3_2.board support p 125 124 .west || decide (bonus 125 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound451 p)
theorem guard452 (p : Pattern) (guard : pushGuard support p 125 124 123 123 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound452 (p : Pattern) (guard : pushGuard support p 125 124 123 123 = true) : bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some 123)) := by
  have certified := compare37 p (guard452 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 124 (some 123))
  have normalized := agree0 _ _ (change_representative support p 124 (some 123) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check452 (p : Pattern) : (!pushGuard support p 125 124 123 123 || decide (bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some 123)))) = true :=
  check_of_implication _ _ (bound452 p)
theorem guard453 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 100 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound453 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 100 .northEast = true) : bonus 125 p ≤ bonus 100 p := by
  have certified := compare103 p (guard453 p guard)
  simpa only [at125, at100, Int.zero_add] using certified
theorem check453 (p : Pattern) : (!walkGuard soko3_2.board support p 125 100 .northEast || decide (bonus 125 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound453 p)
theorem guard454 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 98 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound454 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 98 .northWest = true) : bonus 125 p ≤ bonus 98 p := by
  have certified := compare103 p (guard454 p guard)
  simpa only [at125, at98, Int.zero_add] using certified
theorem check454 (p : Pattern) : (!walkGuard soko3_2.board support p 125 98 .northWest || decide (bonus 125 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound454 p)
theorem guard455 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 152 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound455 (p : Pattern) (guard : walkGuard soko3_2.board support p 125 152 .southEast = true) : bonus 125 p ≤ bonus 152 p := by
  have certified := compare103 p (guard455 p guard)
  simpa only [at125, at152, Int.zero_add] using certified
theorem check455 (p : Pattern) : (!walkGuard soko3_2.board support p 125 152 .southEast || decide (bonus 125 p ≤ bonus 152 p)) = true :=
  check_of_implication _ _ (bound455 p)
end NetHack.Sokoban32Refined
