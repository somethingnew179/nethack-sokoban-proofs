import NetHack.Sokoban22Refined85.ActionBounds034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard840 (p : Pattern) (guard : walkGuard soko2_2.board support p 199 200 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound840 (p : Pattern) (guard : walkGuard soko2_2.board support p 199 200 .east = true) : bonus 199 p ≤ bonus 200 p := by
  have certified := compare0 p (guard840 p guard)
  simpa only [at199, at200, Int.zero_add] using certified
theorem check840 (p : Pattern) : (!walkGuard soko2_2.board support p 199 200 .east || decide (bonus 199 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound840 p)
theorem guard841 (p : Pattern) (guard : pushGuard support p 199 200 201 201 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound841 (p : Pattern) (guard : pushGuard support p 199 200 201 201 = true) : bonus 199 p ≤ 1 + Generated.soko2_2Potential.boulder 201 - Generated.soko2_2Potential.boulder 200 + bonus 200 (change p 200 (some 201)) := by
  have certified := compare0 p (guard841 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 200 (some 201))
  have normalized := agree267 _ _ (change_representative support p 200 (some 201) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check841 (p : Pattern) : (!pushGuard support p 199 200 201 201 || decide (bonus 199 p ≤ 1 + Generated.soko2_2Potential.boulder 201 - Generated.soko2_2Potential.boulder 200 + bonus 200 (change p 200 (some 201)))) = true :=
  check_of_implication _ _ (bound841 p)
theorem guard842 (p : Pattern) (guard : walkGuard soko2_2.board support p 200 201 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound842 (p : Pattern) (guard : walkGuard soko2_2.board support p 200 201 .east = true) : bonus 200 p ≤ bonus 201 p := by
  have certified := compare0 p (guard842 p guard)
  simpa only [at200, at201, Int.zero_add] using certified
theorem check842 (p : Pattern) : (!walkGuard soko2_2.board support p 200 201 .east || decide (bonus 200 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound842 p)
theorem guard843 (p : Pattern) (guard : pushGuard support p 200 201 202 202 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound843 (p : Pattern) (guard : pushGuard support p 200 201 202 202 = true) : bonus 200 p ≤ 1 + Generated.soko2_2Potential.boulder 202 - Generated.soko2_2Potential.boulder 201 + bonus 201 (change p 201 (some 202)) := by
  have certified := compare0 p (guard843 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 201 (some 202))
  have normalized := agree267 _ _ (change_representative support p 201 (some 202) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check843 (p : Pattern) : (!pushGuard support p 200 201 202 202 || decide (bonus 200 p ≤ 1 + Generated.soko2_2Potential.boulder 202 - Generated.soko2_2Potential.boulder 201 + bonus 201 (change p 201 (some 202)))) = true :=
  check_of_implication _ _ (bound843 p)
theorem guard844 (p : Pattern) (guard : walkGuard soko2_2.board support p 200 199 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound844 (p : Pattern) (guard : walkGuard soko2_2.board support p 200 199 .west = true) : bonus 200 p ≤ bonus 199 p := by
  have certified := compare0 p (guard844 p guard)
  simpa only [at200, at199, Int.zero_add] using certified
theorem check844 (p : Pattern) : (!walkGuard soko2_2.board support p 200 199 .west || decide (bonus 200 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound844 p)
theorem guard845 (p : Pattern) (guard : walkGuard soko2_2.board support p 200 177 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound845 (p : Pattern) (guard : walkGuard soko2_2.board support p 200 177 .northWest = true) : bonus 200 p ≤ bonus 177 p := by
  have certified := compare0 p (guard845 p guard)
  simpa only [at200, at177, Int.zero_add] using certified
theorem check845 (p : Pattern) : (!walkGuard soko2_2.board support p 200 177 .northWest || decide (bonus 200 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound845 p)
theorem guard846 (p : Pattern) (guard : walkGuard soko2_2.board support p 200 223 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound846 (p : Pattern) (guard : walkGuard soko2_2.board support p 200 223 .southEast = true) : bonus 200 p ≤ bonus 223 p := by
  have certified := compare0 p (guard846 p guard)
  simpa only [at200, at223, Int.zero_add] using certified
theorem check846 (p : Pattern) : (!walkGuard soko2_2.board support p 200 223 .southEast || decide (bonus 200 p ≤ bonus 223 p)) = true :=
  check_of_implication _ _ (bound846 p)
theorem guard847 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 223 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound847 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 223 .south = true) : bonus 201 p ≤ bonus 223 p := by
  have certified := compare0 p (guard847 p guard)
  simpa only [at201, at223, Int.zero_add] using certified
theorem check847 (p : Pattern) : (!walkGuard soko2_2.board support p 201 223 .south || decide (bonus 201 p ≤ bonus 223 p)) = true :=
  check_of_implication _ _ (bound847 p)
theorem guard848 (p : Pattern) (guard : pushGuard support p 201 223 245 245 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound848 (p : Pattern) (guard : pushGuard support p 201 223 245 245 = true) : bonus 201 p ≤ 1 + Generated.soko2_2Potential.boulder 245 - Generated.soko2_2Potential.boulder 223 + bonus 223 (change p 223 (some 245)) := by
  have certified := compare14199 p (guard848 p guard)
  change d267 p ≤ (5 : Int) + d267 (change p 223 (some 245))
  have normalized := agree267 _ _ (change_representative support p 223 (some 245) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (5 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check848 (p : Pattern) : (!pushGuard support p 201 223 245 245 || decide (bonus 201 p ≤ 1 + Generated.soko2_2Potential.boulder 245 - Generated.soko2_2Potential.boulder 223 + bonus 223 (change p 223 (some 245)))) = true :=
  check_of_implication _ _ (bound848 p)
theorem guard849 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 202 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound849 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 202 .east = true) : bonus 201 p ≤ bonus 202 p := by
  have certified := compare0 p (guard849 p guard)
  simpa only [at201, at202, Int.zero_add] using certified
theorem check849 (p : Pattern) : (!walkGuard soko2_2.board support p 201 202 .east || decide (bonus 201 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound849 p)
theorem guard850 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 200 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound850 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 200 .west = true) : bonus 201 p ≤ bonus 200 p := by
  have certified := compare0 p (guard850 p guard)
  simpa only [at201, at200, Int.zero_add] using certified
theorem check850 (p : Pattern) : (!walkGuard soko2_2.board support p 201 200 .west || decide (bonus 201 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound850 p)
theorem guard851 (p : Pattern) (guard : pushGuard support p 201 200 199 199 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound851 (p : Pattern) (guard : pushGuard support p 201 200 199 199 = true) : bonus 201 p ≤ 1 + Generated.soko2_2Potential.boulder 199 - Generated.soko2_2Potential.boulder 200 + bonus 200 (change p 200 (some 199)) := by
  have certified := compare14199 p (guard851 p guard)
  change d267 p ≤ (5 : Int) + d267 (change p 200 (some 199))
  have normalized := agree267 _ _ (change_representative support p 200 (some 199) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (5 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check851 (p : Pattern) : (!pushGuard support p 201 200 199 199 || decide (bonus 201 p ≤ 1 + Generated.soko2_2Potential.boulder 199 - Generated.soko2_2Potential.boulder 200 + bonus 200 (change p 200 (some 199)))) = true :=
  check_of_implication _ _ (bound851 p)
theorem guard852 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 180 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound852 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 180 .northEast = true) : bonus 201 p ≤ bonus 180 p := by
  have certified := compare0 p (guard852 p guard)
  simpa only [at201, at180, Int.zero_add] using certified
theorem check852 (p : Pattern) : (!walkGuard soko2_2.board support p 201 180 .northEast || decide (bonus 201 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound852 p)
theorem guard853 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 224 .southEast = true) : d4902 p = 1 := by
  change (!false && !(p 224) && !(true && false && false)) = true at guard
  cases h224 : p 224
  all_goals simp [d0, d1, d4902, h224] at guard ⊢
theorem bound853 (p : Pattern) (guard : walkGuard soko2_2.board support p 201 224 .southEast = true) : bonus 201 p ≤ bonus 224 p := by
  have certified := compare14527 p (guard853 p guard)
  simpa only [at201, at224, Int.zero_add] using certified
theorem check853 (p : Pattern) : (!walkGuard soko2_2.board support p 201 224 .southEast || decide (bonus 201 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound853 p)
theorem guard854 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 180 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound854 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 180 .north = true) : bonus 202 p ≤ bonus 180 p := by
  have certified := compare0 p (guard854 p guard)
  simpa only [at202, at180, Int.zero_add] using certified
theorem check854 (p : Pattern) : (!walkGuard soko2_2.board support p 202 180 .north || decide (bonus 202 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound854 p)
theorem guard855 (p : Pattern) (guard : pushGuard support p 202 180 158 158 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound855 (p : Pattern) (guard : pushGuard support p 202 180 158 158 = true) : bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.boulder 180 + bonus 180 (change p 180 (some 158)) := by
  have certified := compare2458 p (guard855 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 180 (some 158))
  have normalized := agree267 _ _ (change_representative support p 180 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check855 (p : Pattern) : (!pushGuard support p 202 180 158 158 || decide (bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.boulder 180 + bonus 180 (change p 180 (some 158)))) = true :=
  check_of_implication _ _ (bound855 p)
theorem guard856 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 224 .south = true) : d4902 p = 1 := by
  change (!false && !(p 224) && !false) = true at guard
  cases h224 : p 224
  all_goals simp [d0, d1, d4902, h224] at guard ⊢
theorem bound856 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 224 .south = true) : bonus 202 p ≤ bonus 224 p := by
  have certified := compare14527 p (guard856 p guard)
  simpa only [at202, at224, Int.zero_add] using certified
theorem check856 (p : Pattern) : (!walkGuard soko2_2.board support p 202 224 .south || decide (bonus 202 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound856 p)
theorem guard857 (p : Pattern) (guard : pushGuard support p 202 224 246 246 = true) : d5269 p = 1 := by
  change (!false && (!true || (p 224)) && !(p 246) && (!(p 246) || false)) = true at guard
  cases h224 : p 224 <;> cases h246 : p 246
  all_goals simp [d0, d1, d5268, d5269, h224, h246] at guard ⊢
theorem bound857 (p : Pattern) (guard : pushGuard support p 202 224 246 246 = true) : bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder 246 - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some 246)) := by
  have certified := compare14830 p (guard857 p guard)
  change d267 p ≤ (0 : Int) + d2502 (change p 224 (some 246))
  have normalized := agree2502 _ _ (change_representative support p 224 (some 246) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d2502 (change p 224 (some 246))
  rw [sub8539]
  exact certified
theorem check857 (p : Pattern) : (!pushGuard support p 202 224 246 246 || decide (bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder 246 - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some 246)))) = true :=
  check_of_implication _ _ (bound857 p)
theorem guard858 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 201 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound858 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 201 .west = true) : bonus 202 p ≤ bonus 201 p := by
  have certified := compare0 p (guard858 p guard)
  simpa only [at202, at201, Int.zero_add] using certified
theorem check858 (p : Pattern) : (!walkGuard soko2_2.board support p 202 201 .west || decide (bonus 202 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound858 p)
theorem guard859 (p : Pattern) (guard : pushGuard support p 202 201 200 200 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound859 (p : Pattern) (guard : pushGuard support p 202 201 200 200 = true) : bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder 200 - Generated.soko2_2Potential.boulder 201 + bonus 201 (change p 201 (some 200)) := by
  have certified := compare2458 p (guard859 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 201 (some 200))
  have normalized := agree267 _ _ (change_representative support p 201 (some 200) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check859 (p : Pattern) : (!pushGuard support p 202 201 200 200 || decide (bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder 200 - Generated.soko2_2Potential.boulder 201 + bonus 201 (change p 201 (some 200)))) = true :=
  check_of_implication _ _ (bound859 p)
theorem guard860 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 181 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound860 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 181 .northEast = true) : bonus 202 p ≤ bonus 181 p := by
  have certified := compare0 p (guard860 p guard)
  simpa only [at202, at181, Int.zero_add] using certified
theorem check860 (p : Pattern) : (!walkGuard soko2_2.board support p 202 181 .northEast || decide (bonus 202 p ≤ bonus 181 p)) = true :=
  check_of_implication _ _ (bound860 p)
theorem guard861 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 225 .southEast = true) : d5503 p = 1 := by
  change (!false && !(p 225) && !(true && (p 224) && true)) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5502, d5503, h224, h225] at guard ⊢
theorem bound861 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 225 .southEast = true) : bonus 202 p ≤ bonus 225 p := by
  have certified := compare15257 p (guard861 p guard)
  simpa only [at202, at225, Int.zero_add] using certified
theorem check861 (p : Pattern) : (!walkGuard soko2_2.board support p 202 225 .southEast || decide (bonus 202 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound861 p)
theorem guard862 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 223 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 224) && false)) = true at guard
  cases h224 : p 224
  all_goals simp [d1, h224] at guard ⊢
theorem bound862 (p : Pattern) (guard : walkGuard soko2_2.board support p 202 223 .southWest = true) : bonus 202 p ≤ bonus 223 p := by
  have certified := compare0 p (guard862 p guard)
  simpa only [at202, at223, Int.zero_add] using certified
theorem check862 (p : Pattern) : (!walkGuard soko2_2.board support p 202 223 .southWest || decide (bonus 202 p ≤ bonus 223 p)) = true :=
  check_of_implication _ _ (bound862 p)
theorem guard863 (p : Pattern) (guard : walkGuard soko2_2.board support p 204 182 .north = true) : d4967 p = 1 := by
  change (!(p 204) && !(p 182) && !false) = true at guard
  cases h182 : p 182 <;> cases h204 : p 204
  all_goals simp [d0, d1, d4474, d4967, h182, h204] at guard ⊢
theorem bound863 (p : Pattern) (guard : walkGuard soko2_2.board support p 204 182 .north = true) : bonus 204 p ≤ bonus 182 p := by
  have certified := compare15667 p (guard863 p guard)
  simpa only [at204, at182, Int.zero_add] using certified
theorem check863 (p : Pattern) : (!walkGuard soko2_2.board support p 204 182 .north || decide (bonus 204 p ≤ bonus 182 p)) = true :=
  check_of_implication _ _ (bound863 p)
end NetHack.Sokoban22Refined85
