import NetHack.Sokoban32Refined.ActionBounds026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard648 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 179 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound648 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 179 .south = true) : bonus 153 p ≤ bonus 179 p := by
  have certified := compare103 p (guard648 p guard)
  simpa only [at153, at179, Int.zero_add] using certified
theorem check648 (p : Pattern) : (!walkGuard soko3_2.board support p 153 179 .south || decide (bonus 153 p ≤ bonus 179 p)) = true :=
  check_of_implication _ _ (bound648 p)
theorem guard649 (p : Pattern) (guard : pushGuard support p 153 179 205 205 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound649 (p : Pattern) (guard : pushGuard support p 153 179 205 205 = true) : bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder 205 - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some 205)) := by
  have certified := compare37 p (guard649 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 179 (some 205))
  have normalized := agree0 _ _ (change_representative support p 179 (some 205) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check649 (p : Pattern) : (!pushGuard support p 153 179 205 205 || decide (bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder 205 - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some 205)))) = true :=
  check_of_implication _ _ (bound649 p)
theorem guard650 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 154 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound650 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 154 .east = true) : bonus 153 p ≤ bonus 154 p := by
  have certified := compare103 p (guard650 p guard)
  simpa only [at153, at154, Int.zero_add] using certified
theorem check650 (p : Pattern) : (!walkGuard soko3_2.board support p 153 154 .east || decide (bonus 153 p ≤ bonus 154 p)) = true :=
  check_of_implication _ _ (bound650 p)
theorem guard651 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 152 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound651 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 152 .west = true) : bonus 153 p ≤ bonus 152 p := by
  have certified := compare103 p (guard651 p guard)
  simpa only [at153, at152, Int.zero_add] using certified
theorem check651 (p : Pattern) : (!walkGuard soko3_2.board support p 153 152 .west || decide (bonus 153 p ≤ bonus 152 p)) = true :=
  check_of_implication _ _ (bound651 p)
theorem guard652 (p : Pattern) (guard : pushGuard support p 153 152 151 151 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound652 (p : Pattern) (guard : pushGuard support p 153 152 151 151 = true) : bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some 151)) := by
  have certified := compare37 p (guard652 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 152 (some 151))
  have normalized := agree0 _ _ (change_representative support p 152 (some 151) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check652 (p : Pattern) : (!pushGuard support p 153 152 151 151 || decide (bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some 151)))) = true :=
  check_of_implication _ _ (bound652 p)
theorem guard653 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 128 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound653 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 128 .northEast = true) : bonus 153 p ≤ bonus 128 p := by
  have certified := compare103 p (guard653 p guard)
  simpa only [at153, at128, Int.zero_add] using certified
theorem check653 (p : Pattern) : (!walkGuard soko3_2.board support p 153 128 .northEast || decide (bonus 153 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound653 p)
theorem guard654 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 126 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound654 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 126 .northWest = true) : bonus 153 p ≤ bonus 126 p := by
  have certified := compare103 p (guard654 p guard)
  simpa only [at153, at126, Int.zero_add] using certified
theorem check654 (p : Pattern) : (!walkGuard soko3_2.board support p 153 126 .northWest || decide (bonus 153 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound654 p)
theorem guard655 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 180 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound655 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 180 .southEast = true) : bonus 153 p ≤ bonus 180 p := by
  have certified := compare103 p (guard655 p guard)
  simpa only [at153, at180, Int.zero_add] using certified
theorem check655 (p : Pattern) : (!walkGuard soko3_2.board support p 153 180 .southEast || decide (bonus 153 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound655 p)
theorem guard656 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 178 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound656 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 178 .southWest = true) : bonus 153 p ≤ bonus 178 p := by
  have certified := compare103 p (guard656 p guard)
  simpa only [at153, at178, Int.zero_add] using certified
theorem check656 (p : Pattern) : (!walkGuard soko3_2.board support p 153 178 .southWest || decide (bonus 153 p ≤ bonus 178 p)) = true :=
  check_of_implication _ _ (bound656 p)
theorem guard657 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 128 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound657 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 128 .north = true) : bonus 154 p ≤ bonus 128 p := by
  have certified := compare103 p (guard657 p guard)
  simpa only [at154, at128, Int.zero_add] using certified
theorem check657 (p : Pattern) : (!walkGuard soko3_2.board support p 154 128 .north || decide (bonus 154 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound657 p)
theorem guard658 (p : Pattern) (guard : pushGuard support p 154 128 102 102 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound658 (p : Pattern) (guard : pushGuard support p 154 128 102 102 = true) : bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder 102 - Generated.soko3_2Potential.boulder 128 + bonus 128 (change p 128 (some 102)) := by
  have certified := compare37 p (guard658 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 128 (some 102))
  have normalized := agree0 _ _ (change_representative support p 128 (some 102) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check658 (p : Pattern) : (!pushGuard support p 154 128 102 102 || decide (bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder 102 - Generated.soko3_2Potential.boulder 128 + bonus 128 (change p 128 (some 102)))) = true :=
  check_of_implication _ _ (bound658 p)
theorem guard659 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 180 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound659 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 180 .south = true) : bonus 154 p ≤ bonus 180 p := by
  have certified := compare103 p (guard659 p guard)
  simpa only [at154, at180, Int.zero_add] using certified
theorem check659 (p : Pattern) : (!walkGuard soko3_2.board support p 154 180 .south || decide (bonus 154 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound659 p)
theorem guard660 (p : Pattern) (guard : pushGuard support p 154 180 206 206 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound660 (p : Pattern) (guard : pushGuard support p 154 180 206 206 = true) : bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder 206 - Generated.soko3_2Potential.boulder 180 + bonus 180 (change p 180 (some 206)) := by
  have certified := compare37 p (guard660 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 180 (some 206))
  have normalized := agree0 _ _ (change_representative support p 180 (some 206) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check660 (p : Pattern) : (!pushGuard support p 154 180 206 206 || decide (bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder 206 - Generated.soko3_2Potential.boulder 180 + bonus 180 (change p 180 (some 206)))) = true :=
  check_of_implication _ _ (bound660 p)
theorem guard661 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 153 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound661 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 153 .west = true) : bonus 154 p ≤ bonus 153 p := by
  have certified := compare103 p (guard661 p guard)
  simpa only [at154, at153, Int.zero_add] using certified
theorem check661 (p : Pattern) : (!walkGuard soko3_2.board support p 154 153 .west || decide (bonus 154 p ≤ bonus 153 p)) = true :=
  check_of_implication _ _ (bound661 p)
theorem guard662 (p : Pattern) (guard : pushGuard support p 154 153 152 152 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound662 (p : Pattern) (guard : pushGuard support p 154 153 152 152 = true) : bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some 152)) := by
  have certified := compare37 p (guard662 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 153 (some 152))
  have normalized := agree0 _ _ (change_representative support p 153 (some 152) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check662 (p : Pattern) : (!pushGuard support p 154 153 152 152 || decide (bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some 152)))) = true :=
  check_of_implication _ _ (bound662 p)
theorem guard663 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 127 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound663 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 127 .northWest = true) : bonus 154 p ≤ bonus 127 p := by
  have certified := compare103 p (guard663 p guard)
  simpa only [at154, at127, Int.zero_add] using certified
theorem check663 (p : Pattern) : (!walkGuard soko3_2.board support p 154 127 .northWest || decide (bonus 154 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound663 p)
theorem guard664 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 179 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound664 (p : Pattern) (guard : walkGuard soko3_2.board support p 154 179 .southWest = true) : bonus 154 p ≤ bonus 179 p := by
  have certified := compare103 p (guard664 p guard)
  simpa only [at154, at179, Int.zero_add] using certified
theorem check664 (p : Pattern) : (!walkGuard soko3_2.board support p 154 179 .southWest || decide (bonus 154 p ≤ bonus 179 p)) = true :=
  check_of_implication _ _ (bound664 p)
theorem guard665 (p : Pattern) (guard : walkGuard soko3_2.board support p 157 131 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound665 (p : Pattern) (guard : walkGuard soko3_2.board support p 157 131 .north = true) : bonus 157 p ≤ bonus 131 p := by
  have certified := compare0 p (guard665 p guard)
  simpa only [at157, at131, Int.zero_add] using certified
theorem check665 (p : Pattern) : (!walkGuard soko3_2.board support p 157 131 .north || decide (bonus 157 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound665 p)
theorem guard666 (p : Pattern) (guard : pushGuard support p 157 131 105 105 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound666 (p : Pattern) (guard : pushGuard support p 157 131 105 105 = true) : bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder 105 - Generated.soko3_2Potential.boulder 131 + bonus 131 (change p 131 (some 105)) := by
  have certified := compare104 p (guard666 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 131 (some 105))
  have normalized := agree134 _ _ (change_representative support p 131 (some 105) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check666 (p : Pattern) : (!pushGuard support p 157 131 105 105 || decide (bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder 105 - Generated.soko3_2Potential.boulder 131 + bonus 131 (change p 131 (some 105)))) = true :=
  check_of_implication _ _ (bound666 p)
theorem guard667 (p : Pattern) (guard : walkGuard soko3_2.board support p 157 183 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound667 (p : Pattern) (guard : walkGuard soko3_2.board support p 157 183 .south = true) : bonus 157 p ≤ bonus 183 p := by
  have certified := compare0 p (guard667 p guard)
  simpa only [at157, at183, Int.zero_add] using certified
theorem check667 (p : Pattern) : (!walkGuard soko3_2.board support p 157 183 .south || decide (bonus 157 p ≤ bonus 183 p)) = true :=
  check_of_implication _ _ (bound667 p)
theorem guard668 (p : Pattern) (guard : pushGuard support p 157 183 209 209 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound668 (p : Pattern) (guard : pushGuard support p 157 183 209 209 = true) : bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder 209 - Generated.soko3_2Potential.boulder 183 + bonus 183 (change p 183 (some 209)) := by
  have certified := compare104 p (guard668 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 183 (some 209))
  have normalized := agree134 _ _ (change_representative support p 183 (some 209) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check668 (p : Pattern) : (!pushGuard support p 157 183 209 209 || decide (bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder 209 - Generated.soko3_2Potential.boulder 183 + bonus 183 (change p 183 (some 209)))) = true :=
  check_of_implication _ _ (bound668 p)
theorem guard669 (p : Pattern) (guard : walkGuard soko3_2.board support p 157 158 .east = true) : d873 p = 1 := by
  change (!false && !(p 158) && !false) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d873, h158] at guard ⊢
theorem bound669 (p : Pattern) (guard : walkGuard soko3_2.board support p 157 158 .east = true) : bonus 157 p ≤ bonus 158 p := by
  have certified := compare2491 p (guard669 p guard)
  simpa only [at157, at158, Int.zero_add] using certified
theorem check669 (p : Pattern) : (!walkGuard soko3_2.board support p 157 158 .east || decide (bonus 157 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound669 p)
theorem guard670 (p : Pattern) (guard : pushGuard support p 157 158 159 159 = true) : d1412 p = 1 := by
  change (!false && (!true || (p 158)) && !(p 159) && (!(p 159) || false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d1167, d1412, h158, h159] at guard ⊢
theorem bound670 (p : Pattern) (guard : pushGuard support p 157 158 159 159 = true) : bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder 159 - Generated.soko3_2Potential.boulder 158 + bonus 158 (change p 158 (some 159)) := by
  have certified := compare6374 p (guard670 p guard)
  change d134 p ≤ (0 : Int) + d652 (change p 158 (some 159))
  have normalized := agree652 _ _ (change_representative support p 158 (some 159) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d652 (change p 158 (some 159))
  rw [sub2716]
  exact certified
theorem check670 (p : Pattern) : (!pushGuard support p 157 158 159 159 || decide (bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder 159 - Generated.soko3_2Potential.boulder 158 + bonus 158 (change p 158 (some 159)))) = true :=
  check_of_implication _ _ (bound670 p)
theorem guard671 (p : Pattern) (guard : walkGuard soko3_2.board support p 157 132 .northEast = true) : d841 p = 1 := by
  change (!false && !(p 132) && !(true && false && (p 158))) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d841, h132, h158] at guard ⊢
theorem bound671 (p : Pattern) (guard : walkGuard soko3_2.board support p 157 132 .northEast = true) : bonus 157 p ≤ bonus 132 p := by
  have certified := compare612 p (guard671 p guard)
  simpa only [at157, at132, Int.zero_add] using certified
theorem check671 (p : Pattern) : (!walkGuard soko3_2.board support p 157 132 .northEast || decide (bonus 157 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound671 p)
end NetHack.Sokoban32Refined
