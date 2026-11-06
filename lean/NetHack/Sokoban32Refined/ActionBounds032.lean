import NetHack.Sokoban32Refined.ActionBounds031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard768 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 174 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound768 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 174 .west = true) : bonus 175 p ≤ bonus 174 p := by
  have certified := compare103 p (guard768 p guard)
  simpa only [at175, at174, Int.zero_add] using certified
theorem check768 (p : Pattern) : (!walkGuard soko3_2.board support p 175 174 .west || decide (bonus 175 p ≤ bonus 174 p)) = true :=
  check_of_implication _ _ (bound768 p)
theorem guard769 (p : Pattern) (guard : pushGuard support p 175 174 173 173 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound769 (p : Pattern) (guard : pushGuard support p 175 174 173 173 = true) : bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some 173)) := by
  have certified := compare37 p (guard769 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 174 (some 173))
  have normalized := agree0 _ _ (change_representative support p 174 (some 173) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check769 (p : Pattern) : (!pushGuard support p 175 174 173 173 || decide (bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some 173)))) = true :=
  check_of_implication _ _ (bound769 p)
theorem guard770 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 150 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound770 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 150 .northEast = true) : bonus 175 p ≤ bonus 150 p := by
  have certified := compare103 p (guard770 p guard)
  simpa only [at175, at150, Int.zero_add] using certified
theorem check770 (p : Pattern) : (!walkGuard soko3_2.board support p 175 150 .northEast || decide (bonus 175 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound770 p)
theorem guard771 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 148 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound771 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 148 .northWest = true) : bonus 175 p ≤ bonus 148 p := by
  have certified := compare103 p (guard771 p guard)
  simpa only [at175, at148, Int.zero_add] using certified
theorem check771 (p : Pattern) : (!walkGuard soko3_2.board support p 175 148 .northWest || decide (bonus 175 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound771 p)
theorem guard772 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 202 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound772 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 202 .southEast = true) : bonus 175 p ≤ bonus 202 p := by
  have certified := compare103 p (guard772 p guard)
  simpa only [at175, at202, Int.zero_add] using certified
theorem check772 (p : Pattern) : (!walkGuard soko3_2.board support p 175 202 .southEast || decide (bonus 175 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound772 p)
theorem guard773 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 200 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound773 (p : Pattern) (guard : walkGuard soko3_2.board support p 175 200 .southWest = true) : bonus 175 p ≤ bonus 200 p := by
  have certified := compare103 p (guard773 p guard)
  simpa only [at175, at200, Int.zero_add] using certified
theorem check773 (p : Pattern) : (!walkGuard soko3_2.board support p 175 200 .southWest || decide (bonus 175 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound773 p)
theorem guard774 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 150 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound774 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 150 .north = true) : bonus 176 p ≤ bonus 150 p := by
  have certified := compare103 p (guard774 p guard)
  simpa only [at176, at150, Int.zero_add] using certified
theorem check774 (p : Pattern) : (!walkGuard soko3_2.board support p 176 150 .north || decide (bonus 176 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound774 p)
theorem guard775 (p : Pattern) (guard : pushGuard support p 176 150 124 124 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound775 (p : Pattern) (guard : pushGuard support p 176 150 124 124 = true) : bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some 124)) := by
  have certified := compare37 p (guard775 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 150 (some 124))
  have normalized := agree0 _ _ (change_representative support p 150 (some 124) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check775 (p : Pattern) : (!pushGuard support p 176 150 124 124 || decide (bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some 124)))) = true :=
  check_of_implication _ _ (bound775 p)
theorem guard776 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 202 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound776 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 202 .south = true) : bonus 176 p ≤ bonus 202 p := by
  have certified := compare103 p (guard776 p guard)
  simpa only [at176, at202, Int.zero_add] using certified
theorem check776 (p : Pattern) : (!walkGuard soko3_2.board support p 176 202 .south || decide (bonus 176 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound776 p)
theorem guard777 (p : Pattern) (guard : pushGuard support p 176 202 228 228 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound777 (p : Pattern) (guard : pushGuard support p 176 202 228 228 = true) : bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder 228 - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some 228)) := by
  have certified := compare37 p (guard777 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 202 (some 228))
  have normalized := agree0 _ _ (change_representative support p 202 (some 228) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check777 (p : Pattern) : (!pushGuard support p 176 202 228 228 || decide (bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder 228 - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some 228)))) = true :=
  check_of_implication _ _ (bound777 p)
theorem guard778 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 177 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound778 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 177 .east = true) : bonus 176 p ≤ bonus 177 p := by
  have certified := compare103 p (guard778 p guard)
  simpa only [at176, at177, Int.zero_add] using certified
theorem check778 (p : Pattern) : (!walkGuard soko3_2.board support p 176 177 .east || decide (bonus 176 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound778 p)
theorem guard779 (p : Pattern) (guard : pushGuard support p 176 177 178 178 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound779 (p : Pattern) (guard : pushGuard support p 176 177 178 178 = true) : bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some 178)) := by
  have certified := compare37 p (guard779 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 177 (some 178))
  have normalized := agree0 _ _ (change_representative support p 177 (some 178) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check779 (p : Pattern) : (!pushGuard support p 176 177 178 178 || decide (bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some 178)))) = true :=
  check_of_implication _ _ (bound779 p)
theorem guard780 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 175 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound780 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 175 .west = true) : bonus 176 p ≤ bonus 175 p := by
  have certified := compare103 p (guard780 p guard)
  simpa only [at176, at175, Int.zero_add] using certified
theorem check780 (p : Pattern) : (!walkGuard soko3_2.board support p 176 175 .west || decide (bonus 176 p ≤ bonus 175 p)) = true :=
  check_of_implication _ _ (bound780 p)
theorem guard781 (p : Pattern) (guard : pushGuard support p 176 175 174 174 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound781 (p : Pattern) (guard : pushGuard support p 176 175 174 174 = true) : bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some 174)) := by
  have certified := compare37 p (guard781 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 175 (some 174))
  have normalized := agree0 _ _ (change_representative support p 175 (some 174) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check781 (p : Pattern) : (!pushGuard support p 176 175 174 174 || decide (bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some 174)))) = true :=
  check_of_implication _ _ (bound781 p)
theorem guard782 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 151 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound782 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 151 .northEast = true) : bonus 176 p ≤ bonus 151 p := by
  have certified := compare103 p (guard782 p guard)
  simpa only [at176, at151, Int.zero_add] using certified
theorem check782 (p : Pattern) : (!walkGuard soko3_2.board support p 176 151 .northEast || decide (bonus 176 p ≤ bonus 151 p)) = true :=
  check_of_implication _ _ (bound782 p)
theorem guard783 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 149 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound783 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 149 .northWest = true) : bonus 176 p ≤ bonus 149 p := by
  have certified := compare103 p (guard783 p guard)
  simpa only [at176, at149, Int.zero_add] using certified
theorem check783 (p : Pattern) : (!walkGuard soko3_2.board support p 176 149 .northWest || decide (bonus 176 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound783 p)
theorem guard784 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 203 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound784 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 203 .southEast = true) : bonus 176 p ≤ bonus 203 p := by
  have certified := compare103 p (guard784 p guard)
  simpa only [at176, at203, Int.zero_add] using certified
theorem check784 (p : Pattern) : (!walkGuard soko3_2.board support p 176 203 .southEast || decide (bonus 176 p ≤ bonus 203 p)) = true :=
  check_of_implication _ _ (bound784 p)
theorem guard785 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 201 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound785 (p : Pattern) (guard : walkGuard soko3_2.board support p 176 201 .southWest = true) : bonus 176 p ≤ bonus 201 p := by
  have certified := compare103 p (guard785 p guard)
  simpa only [at176, at201, Int.zero_add] using certified
theorem check785 (p : Pattern) : (!walkGuard soko3_2.board support p 176 201 .southWest || decide (bonus 176 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound785 p)
theorem guard786 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 151 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound786 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 151 .north = true) : bonus 177 p ≤ bonus 151 p := by
  have certified := compare103 p (guard786 p guard)
  simpa only [at177, at151, Int.zero_add] using certified
theorem check786 (p : Pattern) : (!walkGuard soko3_2.board support p 177 151 .north || decide (bonus 177 p ≤ bonus 151 p)) = true :=
  check_of_implication _ _ (bound786 p)
theorem guard787 (p : Pattern) (guard : pushGuard support p 177 151 125 125 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound787 (p : Pattern) (guard : pushGuard support p 177 151 125 125 = true) : bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some 125)) := by
  have certified := compare37 p (guard787 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 151 (some 125))
  have normalized := agree0 _ _ (change_representative support p 151 (some 125) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check787 (p : Pattern) : (!pushGuard support p 177 151 125 125 || decide (bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some 125)))) = true :=
  check_of_implication _ _ (bound787 p)
theorem guard788 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 203 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound788 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 203 .south = true) : bonus 177 p ≤ bonus 203 p := by
  have certified := compare103 p (guard788 p guard)
  simpa only [at177, at203, Int.zero_add] using certified
theorem check788 (p : Pattern) : (!walkGuard soko3_2.board support p 177 203 .south || decide (bonus 177 p ≤ bonus 203 p)) = true :=
  check_of_implication _ _ (bound788 p)
theorem guard789 (p : Pattern) (guard : pushGuard support p 177 203 229 229 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound789 (p : Pattern) (guard : pushGuard support p 177 203 229 229 = true) : bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder 229 - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some 229)) := by
  have certified := compare37 p (guard789 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 203 (some 229))
  have normalized := agree0 _ _ (change_representative support p 203 (some 229) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check789 (p : Pattern) : (!pushGuard support p 177 203 229 229 || decide (bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder 229 - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some 229)))) = true :=
  check_of_implication _ _ (bound789 p)
theorem guard790 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 178 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound790 (p : Pattern) (guard : walkGuard soko3_2.board support p 177 178 .east = true) : bonus 177 p ≤ bonus 178 p := by
  have certified := compare103 p (guard790 p guard)
  simpa only [at177, at178, Int.zero_add] using certified
theorem check790 (p : Pattern) : (!walkGuard soko3_2.board support p 177 178 .east || decide (bonus 177 p ≤ bonus 178 p)) = true :=
  check_of_implication _ _ (bound790 p)
theorem guard791 (p : Pattern) (guard : pushGuard support p 177 178 179 179 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound791 (p : Pattern) (guard : pushGuard support p 177 178 179 179 = true) : bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some 179)) := by
  have certified := compare37 p (guard791 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 178 (some 179))
  have normalized := agree0 _ _ (change_representative support p 178 (some 179) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check791 (p : Pattern) : (!pushGuard support p 177 178 179 179 || decide (bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some 179)))) = true :=
  check_of_implication _ _ (bound791 p)
end NetHack.Sokoban32Refined
