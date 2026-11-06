import NetHack.Sokoban22Refined85.ActionBounds026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard648 (p : Pattern) (guard : walkGuard soko2_2.board support p 164 186 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound648 (p : Pattern) (guard : walkGuard soko2_2.board support p 164 186 .south = true) : bonus 164 p ≤ bonus 186 p := by
  have certified := compare10636 p (guard648 p guard)
  simpa only [at164, at186, Int.zero_add] using certified
theorem check648 (p : Pattern) : (!walkGuard soko2_2.board support p 164 186 .south || decide (bonus 164 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound648 p)
theorem guard649 (p : Pattern) (guard : walkGuard soko2_2.board support p 164 163 .west = true) : d4148 p = 1 := by
  change (!false && !(p 163) && !false) = true at guard
  cases h163 : p 163
  all_goals simp [d0, d1, d4148, h163] at guard ⊢
theorem bound649 (p : Pattern) (guard : walkGuard soko2_2.board support p 164 163 .west = true) : bonus 164 p ≤ bonus 163 p := by
  have certified := compare10838 p (guard649 p guard)
  simpa only [at164, at163, Int.zero_add] using certified
theorem check649 (p : Pattern) : (!walkGuard soko2_2.board support p 164 163 .west || decide (bonus 164 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound649 p)
theorem guard650 (p : Pattern) (guard : pushGuard support p 164 163 162 162 = true) : d4765 p = 1 := by
  change (!false && (!true || (p 163)) && !(p 162) && (!(p 162) || false)) = true at guard
  cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4147, d4765, h162, h163] at guard ⊢
theorem bound650 (p : Pattern) (guard : pushGuard support p 164 163 162 162 = true) : bonus 164 p ≤ 1 + Generated.soko2_2Potential.boulder 162 - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some 162)) := by
  have certified := compare11089 p (guard650 p guard)
  change d1503 p ≤ (0 : Int) + d1398 (change p 163 (some 162))
  have normalized := agree1398 _ _ (change_representative support p 163 (some 162) 10000 dummy_outside)
  rw [normalized]
  change d1503 p ≤ (0 : Int) + d1398 (change p 163 (some 162))
  rw [sub6557]
  exact certified
theorem check650 (p : Pattern) : (!pushGuard support p 164 163 162 162 || decide (bonus 164 p ≤ 1 + Generated.soko2_2Potential.boulder 162 - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some 162)))) = true :=
  check_of_implication _ _ (bound650 p)
theorem guard651 (p : Pattern) (guard : walkGuard soko2_2.board support p 164 141 .northWest = true) : d4303 p = 1 := by
  change (!false && !(p 141) && !(true && true && (p 163))) = true at guard
  cases h141 : p 141 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4303, h141, h163] at guard ⊢
theorem bound651 (p : Pattern) (guard : walkGuard soko2_2.board support p 164 141 .northWest = true) : bonus 164 p ≤ bonus 141 p := by
  have certified := compare11205 p (guard651 p guard)
  simpa only [at164, at141, Int.zero_add] using certified
theorem check651 (p : Pattern) : (!walkGuard soko2_2.board support p 164 141 .northWest || decide (bonus 164 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound651 p)
theorem guard652 (p : Pattern) (guard : walkGuard soko2_2.board support p 164 185 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 163))) = true at guard
  cases h163 : p 163
  all_goals simp [d1, h163] at guard ⊢
theorem bound652 (p : Pattern) (guard : walkGuard soko2_2.board support p 164 185 .southWest = true) : bonus 164 p ≤ bonus 185 p := by
  have certified := compare10636 p (guard652 p guard)
  simpa only [at164, at185, Int.zero_add] using certified
theorem check652 (p : Pattern) : (!walkGuard soko2_2.board support p 164 185 .southWest || decide (bonus 164 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound652 p)
theorem guard653 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 144 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound653 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 144 .north = true) : bonus 166 p ≤ bonus 144 p := by
  have certified := compare1086 p (guard653 p guard)
  simpa only [at166, at144, Int.zero_add] using certified
theorem check653 (p : Pattern) : (!walkGuard soko2_2.board support p 166 144 .north || decide (bonus 166 p ≤ bonus 144 p)) = true :=
  check_of_implication _ _ (bound653 p)
theorem guard654 (p : Pattern) (guard : pushGuard support p 166 144 122 122 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound654 (p : Pattern) (guard : pushGuard support p 166 144 122 122 = true) : bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder 122 - Generated.soko2_2Potential.boulder 144 + bonus 144 (change p 144 (some 122)) := by
  have certified := compare1087 p (guard654 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 144 (some 122))
  have normalized := agree0 _ _ (change_representative support p 144 (some 122) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check654 (p : Pattern) : (!pushGuard support p 166 144 122 122 || decide (bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder 122 - Generated.soko2_2Potential.boulder 144 + bonus 144 (change p 144 (some 122)))) = true :=
  check_of_implication _ _ (bound654 p)
theorem guard655 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 188 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound655 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 188 .south = true) : bonus 166 p ≤ bonus 188 p := by
  have certified := compare1086 p (guard655 p guard)
  simpa only [at166, at188, Int.zero_add] using certified
theorem check655 (p : Pattern) : (!walkGuard soko2_2.board support p 166 188 .south || decide (bonus 166 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound655 p)
theorem guard656 (p : Pattern) (guard : pushGuard support p 166 188 210 210 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound656 (p : Pattern) (guard : pushGuard support p 166 188 210 210 = true) : bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder 210 - Generated.soko2_2Potential.boulder 188 + bonus 188 (change p 188 (some 210)) := by
  have certified := compare1087 p (guard656 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 188 (some 210))
  have normalized := agree0 _ _ (change_representative support p 188 (some 210) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check656 (p : Pattern) : (!pushGuard support p 166 188 210 210 || decide (bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder 210 - Generated.soko2_2Potential.boulder 188 + bonus 188 (change p 188 (some 210)))) = true :=
  check_of_implication _ _ (bound656 p)
theorem guard657 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 167 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound657 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 167 .east = true) : bonus 166 p ≤ bonus 167 p := by
  have certified := compare1086 p (guard657 p guard)
  simpa only [at166, at167, Int.zero_add] using certified
theorem check657 (p : Pattern) : (!walkGuard soko2_2.board support p 166 167 .east || decide (bonus 166 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound657 p)
theorem guard658 (p : Pattern) (guard : pushGuard support p 166 167 168 168 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound658 (p : Pattern) (guard : pushGuard support p 166 167 168 168 = true) : bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some 168)) := by
  have certified := compare1087 p (guard658 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 167 (some 168))
  have normalized := agree0 _ _ (change_representative support p 167 (some 168) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check658 (p : Pattern) : (!pushGuard support p 166 167 168 168 || decide (bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some 168)))) = true :=
  check_of_implication _ _ (bound658 p)
theorem guard659 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 145 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound659 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 145 .northEast = true) : bonus 166 p ≤ bonus 145 p := by
  have certified := compare1086 p (guard659 p guard)
  simpa only [at166, at145, Int.zero_add] using certified
theorem check659 (p : Pattern) : (!walkGuard soko2_2.board support p 166 145 .northEast || decide (bonus 166 p ≤ bonus 145 p)) = true :=
  check_of_implication _ _ (bound659 p)
theorem guard660 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 189 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound660 (p : Pattern) (guard : walkGuard soko2_2.board support p 166 189 .southEast = true) : bonus 166 p ≤ bonus 189 p := by
  have certified := compare1086 p (guard660 p guard)
  simpa only [at166, at189, Int.zero_add] using certified
theorem check660 (p : Pattern) : (!walkGuard soko2_2.board support p 166 189 .southEast || decide (bonus 166 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound660 p)
theorem guard661 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 145 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound661 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 145 .north = true) : bonus 167 p ≤ bonus 145 p := by
  have certified := compare1086 p (guard661 p guard)
  simpa only [at167, at145, Int.zero_add] using certified
theorem check661 (p : Pattern) : (!walkGuard soko2_2.board support p 167 145 .north || decide (bonus 167 p ≤ bonus 145 p)) = true :=
  check_of_implication _ _ (bound661 p)
theorem guard662 (p : Pattern) (guard : pushGuard support p 167 145 123 123 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound662 (p : Pattern) (guard : pushGuard support p 167 145 123 123 = true) : bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some 123)) := by
  have certified := compare1087 p (guard662 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 145 (some 123))
  have normalized := agree0 _ _ (change_representative support p 145 (some 123) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check662 (p : Pattern) : (!pushGuard support p 167 145 123 123 || decide (bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some 123)))) = true :=
  check_of_implication _ _ (bound662 p)
theorem guard663 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 189 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound663 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 189 .south = true) : bonus 167 p ≤ bonus 189 p := by
  have certified := compare1086 p (guard663 p guard)
  simpa only [at167, at189, Int.zero_add] using certified
theorem check663 (p : Pattern) : (!walkGuard soko2_2.board support p 167 189 .south || decide (bonus 167 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound663 p)
theorem guard664 (p : Pattern) (guard : pushGuard support p 167 189 211 211 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound664 (p : Pattern) (guard : pushGuard support p 167 189 211 211 = true) : bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder 211 - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some 211)) := by
  have certified := compare1087 p (guard664 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 189 (some 211))
  have normalized := agree0 _ _ (change_representative support p 189 (some 211) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check664 (p : Pattern) : (!pushGuard support p 167 189 211 211 || decide (bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder 211 - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some 211)))) = true :=
  check_of_implication _ _ (bound664 p)
theorem guard665 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 168 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound665 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 168 .east = true) : bonus 167 p ≤ bonus 168 p := by
  have certified := compare1086 p (guard665 p guard)
  simpa only [at167, at168, Int.zero_add] using certified
theorem check665 (p : Pattern) : (!walkGuard soko2_2.board support p 167 168 .east || decide (bonus 167 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound665 p)
theorem guard666 (p : Pattern) (guard : pushGuard support p 167 168 169 169 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound666 (p : Pattern) (guard : pushGuard support p 167 168 169 169 = true) : bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some 169)) := by
  have certified := compare1087 p (guard666 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 168 (some 169))
  have normalized := agree0 _ _ (change_representative support p 168 (some 169) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check666 (p : Pattern) : (!pushGuard support p 167 168 169 169 || decide (bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some 169)))) = true :=
  check_of_implication _ _ (bound666 p)
theorem guard667 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 166 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound667 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 166 .west = true) : bonus 167 p ≤ bonus 166 p := by
  have certified := compare1086 p (guard667 p guard)
  simpa only [at167, at166, Int.zero_add] using certified
theorem check667 (p : Pattern) : (!walkGuard soko2_2.board support p 167 166 .west || decide (bonus 167 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound667 p)
theorem guard668 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 146 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound668 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 146 .northEast = true) : bonus 167 p ≤ bonus 146 p := by
  have certified := compare1086 p (guard668 p guard)
  simpa only [at167, at146, Int.zero_add] using certified
theorem check668 (p : Pattern) : (!walkGuard soko2_2.board support p 167 146 .northEast || decide (bonus 167 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound668 p)
theorem guard669 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 144 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound669 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 144 .northWest = true) : bonus 167 p ≤ bonus 144 p := by
  have certified := compare1086 p (guard669 p guard)
  simpa only [at167, at144, Int.zero_add] using certified
theorem check669 (p : Pattern) : (!walkGuard soko2_2.board support p 167 144 .northWest || decide (bonus 167 p ≤ bonus 144 p)) = true :=
  check_of_implication _ _ (bound669 p)
theorem guard670 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 190 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound670 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 190 .southEast = true) : bonus 167 p ≤ bonus 190 p := by
  have certified := compare1086 p (guard670 p guard)
  simpa only [at167, at190, Int.zero_add] using certified
theorem check670 (p : Pattern) : (!walkGuard soko2_2.board support p 167 190 .southEast || decide (bonus 167 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound670 p)
theorem guard671 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 188 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound671 (p : Pattern) (guard : walkGuard soko2_2.board support p 167 188 .southWest = true) : bonus 167 p ≤ bonus 188 p := by
  have certified := compare1086 p (guard671 p guard)
  simpa only [at167, at188, Int.zero_add] using certified
theorem check671 (p : Pattern) : (!walkGuard soko2_2.board support p 167 188 .southWest || decide (bonus 167 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound671 p)
end NetHack.Sokoban22Refined85
