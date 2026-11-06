import NetHack.Sokoban22Refined85.ActionBounds022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard552 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 127 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound552 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 127 .northEast = true) : bonus 148 p ≤ bonus 127 p := by
  have certified := compare1086 p (guard552 p guard)
  simpa only [at148, at127, Int.zero_add] using certified
theorem check552 (p : Pattern) : (!walkGuard soko2_2.board support p 148 127 .northEast || decide (bonus 148 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound552 p)
theorem guard553 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 125 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound553 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 125 .northWest = true) : bonus 148 p ≤ bonus 125 p := by
  have certified := compare1086 p (guard553 p guard)
  simpa only [at148, at125, Int.zero_add] using certified
theorem check553 (p : Pattern) : (!walkGuard soko2_2.board support p 148 125 .northWest || decide (bonus 148 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound553 p)
theorem guard554 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 171 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound554 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 171 .southEast = true) : bonus 148 p ≤ bonus 171 p := by
  have certified := compare1086 p (guard554 p guard)
  simpa only [at148, at171, Int.zero_add] using certified
theorem check554 (p : Pattern) : (!walkGuard soko2_2.board support p 148 171 .southEast || decide (bonus 148 p ≤ bonus 171 p)) = true :=
  check_of_implication _ _ (bound554 p)
theorem guard555 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 169 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound555 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 169 .southWest = true) : bonus 148 p ≤ bonus 169 p := by
  have certified := compare1086 p (guard555 p guard)
  simpa only [at148, at169, Int.zero_add] using certified
theorem check555 (p : Pattern) : (!walkGuard soko2_2.board support p 148 169 .southWest || decide (bonus 148 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound555 p)
theorem guard556 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 127 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound556 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 127 .north = true) : bonus 149 p ≤ bonus 127 p := by
  have certified := compare1086 p (guard556 p guard)
  simpa only [at149, at127, Int.zero_add] using certified
theorem check556 (p : Pattern) : (!walkGuard soko2_2.board support p 149 127 .north || decide (bonus 149 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound556 p)
theorem guard557 (p : Pattern) (guard : pushGuard support p 149 127 105 105 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound557 (p : Pattern) (guard : pushGuard support p 149 127 105 105 = true) : bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder 105 - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some 105)) := by
  have certified := compare1087 p (guard557 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 127 (some 105))
  have normalized := agree0 _ _ (change_representative support p 127 (some 105) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check557 (p : Pattern) : (!pushGuard support p 149 127 105 105 || decide (bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder 105 - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some 105)))) = true :=
  check_of_implication _ _ (bound557 p)
theorem guard558 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 171 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound558 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 171 .south = true) : bonus 149 p ≤ bonus 171 p := by
  have certified := compare1086 p (guard558 p guard)
  simpa only [at149, at171, Int.zero_add] using certified
theorem check558 (p : Pattern) : (!walkGuard soko2_2.board support p 149 171 .south || decide (bonus 149 p ≤ bonus 171 p)) = true :=
  check_of_implication _ _ (bound558 p)
theorem guard559 (p : Pattern) (guard : pushGuard support p 149 171 193 193 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound559 (p : Pattern) (guard : pushGuard support p 149 171 193 193 = true) : bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder 193 - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some 193)) := by
  have certified := compare1087 p (guard559 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 171 (some 193))
  have normalized := agree0 _ _ (change_representative support p 171 (some 193) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check559 (p : Pattern) : (!pushGuard support p 149 171 193 193 || decide (bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder 193 - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some 193)))) = true :=
  check_of_implication _ _ (bound559 p)
theorem guard560 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 150 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound560 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 150 .east = true) : bonus 149 p ≤ bonus 150 p := by
  have certified := compare1086 p (guard560 p guard)
  simpa only [at149, at150, Int.zero_add] using certified
theorem check560 (p : Pattern) : (!walkGuard soko2_2.board support p 149 150 .east || decide (bonus 149 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound560 p)
theorem guard561 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 148 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound561 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 148 .west = true) : bonus 149 p ≤ bonus 148 p := by
  have certified := compare1086 p (guard561 p guard)
  simpa only [at149, at148, Int.zero_add] using certified
theorem check561 (p : Pattern) : (!walkGuard soko2_2.board support p 149 148 .west || decide (bonus 149 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound561 p)
theorem guard562 (p : Pattern) (guard : pushGuard support p 149 148 147 147 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound562 (p : Pattern) (guard : pushGuard support p 149 148 147 147 = true) : bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some 147)) := by
  have certified := compare1087 p (guard562 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 148 (some 147))
  have normalized := agree0 _ _ (change_representative support p 148 (some 147) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check562 (p : Pattern) : (!pushGuard support p 149 148 147 147 || decide (bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some 147)))) = true :=
  check_of_implication _ _ (bound562 p)
theorem guard563 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 128 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound563 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 128 .northEast = true) : bonus 149 p ≤ bonus 128 p := by
  have certified := compare1086 p (guard563 p guard)
  simpa only [at149, at128, Int.zero_add] using certified
theorem check563 (p : Pattern) : (!walkGuard soko2_2.board support p 149 128 .northEast || decide (bonus 149 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound563 p)
theorem guard564 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 126 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound564 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 126 .northWest = true) : bonus 149 p ≤ bonus 126 p := by
  have certified := compare1086 p (guard564 p guard)
  simpa only [at149, at126, Int.zero_add] using certified
theorem check564 (p : Pattern) : (!walkGuard soko2_2.board support p 149 126 .northWest || decide (bonus 149 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound564 p)
theorem guard565 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 172 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound565 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 172 .southEast = true) : bonus 149 p ≤ bonus 172 p := by
  have certified := compare1086 p (guard565 p guard)
  simpa only [at149, at172, Int.zero_add] using certified
theorem check565 (p : Pattern) : (!walkGuard soko2_2.board support p 149 172 .southEast || decide (bonus 149 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound565 p)
theorem guard566 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 170 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound566 (p : Pattern) (guard : walkGuard soko2_2.board support p 149 170 .southWest = true) : bonus 149 p ≤ bonus 170 p := by
  have certified := compare1086 p (guard566 p guard)
  simpa only [at149, at170, Int.zero_add] using certified
theorem check566 (p : Pattern) : (!walkGuard soko2_2.board support p 149 170 .southWest || decide (bonus 149 p ≤ bonus 170 p)) = true :=
  check_of_implication _ _ (bound566 p)
theorem guard567 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 128 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound567 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 128 .north = true) : bonus 150 p ≤ bonus 128 p := by
  have certified := compare1086 p (guard567 p guard)
  simpa only [at150, at128, Int.zero_add] using certified
theorem check567 (p : Pattern) : (!walkGuard soko2_2.board support p 150 128 .north || decide (bonus 150 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound567 p)
theorem guard568 (p : Pattern) (guard : pushGuard support p 150 128 106 106 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound568 (p : Pattern) (guard : pushGuard support p 150 128 106 106 = true) : bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder 106 - Generated.soko2_2Potential.boulder 128 + bonus 128 (change p 128 (some 106)) := by
  have certified := compare1087 p (guard568 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 128 (some 106))
  have normalized := agree0 _ _ (change_representative support p 128 (some 106) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check568 (p : Pattern) : (!pushGuard support p 150 128 106 106 || decide (bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder 106 - Generated.soko2_2Potential.boulder 128 + bonus 128 (change p 128 (some 106)))) = true :=
  check_of_implication _ _ (bound568 p)
theorem guard569 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 172 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound569 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 172 .south = true) : bonus 150 p ≤ bonus 172 p := by
  have certified := compare1086 p (guard569 p guard)
  simpa only [at150, at172, Int.zero_add] using certified
theorem check569 (p : Pattern) : (!walkGuard soko2_2.board support p 150 172 .south || decide (bonus 150 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound569 p)
theorem guard570 (p : Pattern) (guard : pushGuard support p 150 172 194 194 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound570 (p : Pattern) (guard : pushGuard support p 150 172 194 194 = true) : bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder 194 - Generated.soko2_2Potential.boulder 172 + bonus 172 (change p 172 (some 194)) := by
  have certified := compare1087 p (guard570 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 172 (some 194))
  have normalized := agree0 _ _ (change_representative support p 172 (some 194) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check570 (p : Pattern) : (!pushGuard support p 150 172 194 194 || decide (bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder 194 - Generated.soko2_2Potential.boulder 172 + bonus 172 (change p 172 (some 194)))) = true :=
  check_of_implication _ _ (bound570 p)
theorem guard571 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 149 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound571 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 149 .west = true) : bonus 150 p ≤ bonus 149 p := by
  have certified := compare1086 p (guard571 p guard)
  simpa only [at150, at149, Int.zero_add] using certified
theorem check571 (p : Pattern) : (!walkGuard soko2_2.board support p 150 149 .west || decide (bonus 150 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound571 p)
theorem guard572 (p : Pattern) (guard : pushGuard support p 150 149 148 148 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound572 (p : Pattern) (guard : pushGuard support p 150 149 148 148 = true) : bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some 148)) := by
  have certified := compare1087 p (guard572 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 149 (some 148))
  have normalized := agree0 _ _ (change_representative support p 149 (some 148) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check572 (p : Pattern) : (!pushGuard support p 150 149 148 148 || decide (bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some 148)))) = true :=
  check_of_implication _ _ (bound572 p)
theorem guard573 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 127 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound573 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 127 .northWest = true) : bonus 150 p ≤ bonus 127 p := by
  have certified := compare1086 p (guard573 p guard)
  simpa only [at150, at127, Int.zero_add] using certified
theorem check573 (p : Pattern) : (!walkGuard soko2_2.board support p 150 127 .northWest || decide (bonus 150 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound573 p)
theorem guard574 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 171 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound574 (p : Pattern) (guard : walkGuard soko2_2.board support p 150 171 .southWest = true) : bonus 150 p ≤ bonus 171 p := by
  have certified := compare1086 p (guard574 p guard)
  simpa only [at150, at171, Int.zero_add] using certified
theorem check574 (p : Pattern) : (!walkGuard soko2_2.board support p 150 171 .southWest || decide (bonus 150 p ≤ bonus 171 p)) = true :=
  check_of_implication _ _ (bound574 p)
theorem guard575 (p : Pattern) (guard : walkGuard soko2_2.board support p 155 133 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound575 (p : Pattern) (guard : walkGuard soko2_2.board support p 155 133 .north = true) : bonus 155 p ≤ bonus 133 p := by
  have certified := compare0 p (guard575 p guard)
  simpa only [at155, at133, Int.zero_add] using certified
theorem check575 (p : Pattern) : (!walkGuard soko2_2.board support p 155 133 .north || decide (bonus 155 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound575 p)
end NetHack.Sokoban22Refined85
