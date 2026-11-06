import NetHack.Sokoban22Refined85.ActionBounds031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard768 (p : Pattern) (guard : walkGuard soko2_2.board support p 186 185 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound768 (p : Pattern) (guard : walkGuard soko2_2.board support p 186 185 .west = true) : bonus 186 p ≤ bonus 185 p := by
  have certified := compare10636 p (guard768 p guard)
  simpa only [at186, at185, Int.zero_add] using certified
theorem check768 (p : Pattern) : (!walkGuard soko2_2.board support p 186 185 .west || decide (bonus 186 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound768 p)
theorem guard769 (p : Pattern) (guard : pushGuard support p 186 185 184 184 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound769 (p : Pattern) (guard : pushGuard support p 186 185 184 184 = true) : bonus 186 p ≤ 1 + Generated.soko2_2Potential.boulder 184 - Generated.soko2_2Potential.boulder 185 + bonus 185 (change p 185 (some 184)) := by
  have certified := compare13828 p (guard769 p guard)
  change d1503 p ≤ (1 : Int) + d1503 (change p 185 (some 184))
  have normalized := agree1503 _ _ (change_representative support p 185 (some 184) 10000 dummy_outside)
  rw [normalized]
  change d1503 p ≤ (1 : Int) + d1503 (change p 10000 none)
  rw [sub7977]
  exact certified
theorem check769 (p : Pattern) : (!pushGuard support p 186 185 184 184 || decide (bonus 186 p ≤ 1 + Generated.soko2_2Potential.boulder 184 - Generated.soko2_2Potential.boulder 185 + bonus 185 (change p 185 (some 184)))) = true :=
  check_of_implication _ _ (bound769 p)
theorem guard770 (p : Pattern) (guard : walkGuard soko2_2.board support p 186 163 .northWest = true) : d4148 p = 1 := by
  change (!false && !(p 163) && !(true && false && false)) = true at guard
  cases h163 : p 163
  all_goals simp [d0, d1, d4148, h163] at guard ⊢
theorem bound770 (p : Pattern) (guard : walkGuard soko2_2.board support p 186 163 .northWest = true) : bonus 186 p ≤ bonus 163 p := by
  have certified := compare10838 p (guard770 p guard)
  simpa only [at186, at163, Int.zero_add] using certified
theorem check770 (p : Pattern) : (!walkGuard soko2_2.board support p 186 163 .northWest || decide (bonus 186 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound770 p)
theorem guard771 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 166 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound771 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 166 .north = true) : bonus 188 p ≤ bonus 166 p := by
  have certified := compare1086 p (guard771 p guard)
  simpa only [at188, at166, Int.zero_add] using certified
theorem check771 (p : Pattern) : (!walkGuard soko2_2.board support p 188 166 .north || decide (bonus 188 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound771 p)
theorem guard772 (p : Pattern) (guard : pushGuard support p 188 166 144 144 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound772 (p : Pattern) (guard : pushGuard support p 188 166 144 144 = true) : bonus 188 p ≤ 1 + Generated.soko2_2Potential.boulder 144 - Generated.soko2_2Potential.boulder 166 + bonus 166 (change p 166 (some 144)) := by
  have certified := compare1087 p (guard772 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 166 (some 144))
  have normalized := agree0 _ _ (change_representative support p 166 (some 144) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check772 (p : Pattern) : (!pushGuard support p 188 166 144 144 || decide (bonus 188 p ≤ 1 + Generated.soko2_2Potential.boulder 144 - Generated.soko2_2Potential.boulder 166 + bonus 166 (change p 166 (some 144)))) = true :=
  check_of_implication _ _ (bound772 p)
theorem guard773 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 210 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound773 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 210 .south = true) : bonus 188 p ≤ bonus 210 p := by
  have certified := compare1086 p (guard773 p guard)
  simpa only [at188, at210, Int.zero_add] using certified
theorem check773 (p : Pattern) : (!walkGuard soko2_2.board support p 188 210 .south || decide (bonus 188 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound773 p)
theorem guard774 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 189 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound774 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 189 .east = true) : bonus 188 p ≤ bonus 189 p := by
  have certified := compare1086 p (guard774 p guard)
  simpa only [at188, at189, Int.zero_add] using certified
theorem check774 (p : Pattern) : (!walkGuard soko2_2.board support p 188 189 .east || decide (bonus 188 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound774 p)
theorem guard775 (p : Pattern) (guard : pushGuard support p 188 189 190 190 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound775 (p : Pattern) (guard : pushGuard support p 188 189 190 190 = true) : bonus 188 p ≤ 1 + Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some 190)) := by
  have certified := compare1087 p (guard775 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 189 (some 190))
  have normalized := agree0 _ _ (change_representative support p 189 (some 190) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check775 (p : Pattern) : (!pushGuard support p 188 189 190 190 || decide (bonus 188 p ≤ 1 + Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some 190)))) = true :=
  check_of_implication _ _ (bound775 p)
theorem guard776 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 167 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound776 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 167 .northEast = true) : bonus 188 p ≤ bonus 167 p := by
  have certified := compare1086 p (guard776 p guard)
  simpa only [at188, at167, Int.zero_add] using certified
theorem check776 (p : Pattern) : (!walkGuard soko2_2.board support p 188 167 .northEast || decide (bonus 188 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound776 p)
theorem guard777 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 211 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound777 (p : Pattern) (guard : walkGuard soko2_2.board support p 188 211 .southEast = true) : bonus 188 p ≤ bonus 211 p := by
  have certified := compare1086 p (guard777 p guard)
  simpa only [at188, at211, Int.zero_add] using certified
theorem check777 (p : Pattern) : (!walkGuard soko2_2.board support p 188 211 .southEast || decide (bonus 188 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound777 p)
theorem guard778 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 167 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound778 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 167 .north = true) : bonus 189 p ≤ bonus 167 p := by
  have certified := compare1086 p (guard778 p guard)
  simpa only [at189, at167, Int.zero_add] using certified
theorem check778 (p : Pattern) : (!walkGuard soko2_2.board support p 189 167 .north || decide (bonus 189 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound778 p)
theorem guard779 (p : Pattern) (guard : pushGuard support p 189 167 145 145 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound779 (p : Pattern) (guard : pushGuard support p 189 167 145 145 = true) : bonus 189 p ≤ 1 + Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some 145)) := by
  have certified := compare1087 p (guard779 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 167 (some 145))
  have normalized := agree0 _ _ (change_representative support p 167 (some 145) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check779 (p : Pattern) : (!pushGuard support p 189 167 145 145 || decide (bonus 189 p ≤ 1 + Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some 145)))) = true :=
  check_of_implication _ _ (bound779 p)
theorem guard780 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 211 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound780 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 211 .south = true) : bonus 189 p ≤ bonus 211 p := by
  have certified := compare1086 p (guard780 p guard)
  simpa only [at189, at211, Int.zero_add] using certified
theorem check780 (p : Pattern) : (!walkGuard soko2_2.board support p 189 211 .south || decide (bonus 189 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound780 p)
theorem guard781 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 190 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound781 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 190 .east = true) : bonus 189 p ≤ bonus 190 p := by
  have certified := compare1086 p (guard781 p guard)
  simpa only [at189, at190, Int.zero_add] using certified
theorem check781 (p : Pattern) : (!walkGuard soko2_2.board support p 189 190 .east || decide (bonus 189 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound781 p)
theorem guard782 (p : Pattern) (guard : pushGuard support p 189 190 191 191 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound782 (p : Pattern) (guard : pushGuard support p 189 190 191 191 = true) : bonus 189 p ≤ 1 + Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some 191)) := by
  have certified := compare1087 p (guard782 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 190 (some 191))
  have normalized := agree0 _ _ (change_representative support p 190 (some 191) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check782 (p : Pattern) : (!pushGuard support p 189 190 191 191 || decide (bonus 189 p ≤ 1 + Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some 191)))) = true :=
  check_of_implication _ _ (bound782 p)
theorem guard783 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 188 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound783 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 188 .west = true) : bonus 189 p ≤ bonus 188 p := by
  have certified := compare1086 p (guard783 p guard)
  simpa only [at189, at188, Int.zero_add] using certified
theorem check783 (p : Pattern) : (!walkGuard soko2_2.board support p 189 188 .west || decide (bonus 189 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound783 p)
theorem guard784 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 168 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound784 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 168 .northEast = true) : bonus 189 p ≤ bonus 168 p := by
  have certified := compare1086 p (guard784 p guard)
  simpa only [at189, at168, Int.zero_add] using certified
theorem check784 (p : Pattern) : (!walkGuard soko2_2.board support p 189 168 .northEast || decide (bonus 189 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound784 p)
theorem guard785 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 166 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound785 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 166 .northWest = true) : bonus 189 p ≤ bonus 166 p := by
  have certified := compare1086 p (guard785 p guard)
  simpa only [at189, at166, Int.zero_add] using certified
theorem check785 (p : Pattern) : (!walkGuard soko2_2.board support p 189 166 .northWest || decide (bonus 189 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound785 p)
theorem guard786 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 212 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound786 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 212 .southEast = true) : bonus 189 p ≤ bonus 212 p := by
  have certified := compare1086 p (guard786 p guard)
  simpa only [at189, at212, Int.zero_add] using certified
theorem check786 (p : Pattern) : (!walkGuard soko2_2.board support p 189 212 .southEast || decide (bonus 189 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound786 p)
theorem guard787 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 210 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound787 (p : Pattern) (guard : walkGuard soko2_2.board support p 189 210 .southWest = true) : bonus 189 p ≤ bonus 210 p := by
  have certified := compare1086 p (guard787 p guard)
  simpa only [at189, at210, Int.zero_add] using certified
theorem check787 (p : Pattern) : (!walkGuard soko2_2.board support p 189 210 .southWest || decide (bonus 189 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound787 p)
theorem guard788 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 168 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound788 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 168 .north = true) : bonus 190 p ≤ bonus 168 p := by
  have certified := compare1086 p (guard788 p guard)
  simpa only [at190, at168, Int.zero_add] using certified
theorem check788 (p : Pattern) : (!walkGuard soko2_2.board support p 190 168 .north || decide (bonus 190 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound788 p)
theorem guard789 (p : Pattern) (guard : pushGuard support p 190 168 146 146 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound789 (p : Pattern) (guard : pushGuard support p 190 168 146 146 = true) : bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some 146)) := by
  have certified := compare1087 p (guard789 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 168 (some 146))
  have normalized := agree0 _ _ (change_representative support p 168 (some 146) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check789 (p : Pattern) : (!pushGuard support p 190 168 146 146 || decide (bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some 146)))) = true :=
  check_of_implication _ _ (bound789 p)
theorem guard790 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 212 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound790 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 212 .south = true) : bonus 190 p ≤ bonus 212 p := by
  have certified := compare1086 p (guard790 p guard)
  simpa only [at190, at212, Int.zero_add] using certified
theorem check790 (p : Pattern) : (!walkGuard soko2_2.board support p 190 212 .south || decide (bonus 190 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound790 p)
theorem guard791 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 191 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound791 (p : Pattern) (guard : walkGuard soko2_2.board support p 190 191 .east = true) : bonus 190 p ≤ bonus 191 p := by
  have certified := compare1086 p (guard791 p guard)
  simpa only [at190, at191, Int.zero_add] using certified
theorem check791 (p : Pattern) : (!walkGuard soko2_2.board support p 190 191 .east || decide (bonus 190 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound791 p)
end NetHack.Sokoban22Refined85
