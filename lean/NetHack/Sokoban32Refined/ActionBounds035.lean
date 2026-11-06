import NetHack.Sokoban32Refined.ActionBounds034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard840 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 161 .northWest = true) : d985 p = 1 := by
  change (!false && !(p 161) && !(true && false && true)) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound840 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 161 .northWest = true) : bonus 188 p ≤ bonus 161 p := by
  have certified := compare4300 p (guard840 p guard)
  simpa only [at188, at161, Int.zero_add] using certified
theorem check840 (p : Pattern) : (!walkGuard soko3_2.board support p 188 161 .northWest || decide (bonus 188 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound840 p)
theorem guard841 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 215 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound841 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 215 .southEast = true) : bonus 188 p ≤ bonus 215 p := by
  have certified := compare0 p (guard841 p guard)
  simpa only [at188, at215, Int.zero_add] using certified
theorem check841 (p : Pattern) : (!walkGuard soko3_2.board support p 188 215 .southEast || decide (bonus 188 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound841 p)
theorem guard842 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 213 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound842 (p : Pattern) (guard : walkGuard soko3_2.board support p 188 213 .southWest = true) : bonus 188 p ≤ bonus 213 p := by
  have certified := compare0 p (guard842 p guard)
  simpa only [at188, at213, Int.zero_add] using certified
theorem check842 (p : Pattern) : (!walkGuard soko3_2.board support p 188 213 .southWest || decide (bonus 188 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound842 p)
theorem guard843 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 163 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound843 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 163 .north = true) : bonus 189 p ≤ bonus 163 p := by
  have certified := compare0 p (guard843 p guard)
  simpa only [at189, at163, Int.zero_add] using certified
theorem check843 (p : Pattern) : (!walkGuard soko3_2.board support p 189 163 .north || decide (bonus 189 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound843 p)
theorem guard844 (p : Pattern) (guard : pushGuard support p 189 163 137 137 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound844 (p : Pattern) (guard : pushGuard support p 189 163 137 137 = true) : bonus 189 p ≤ 1 + Generated.soko3_2Potential.boulder 137 - Generated.soko3_2Potential.boulder 163 + bonus 163 (change p 163 (some 137)) := by
  have certified := compare9360 p (guard844 p guard)
  change d134 p ≤ (4 : Int) + d134 (change p 163 (some 137))
  have normalized := agree134 _ _ (change_representative support p 163 (some 137) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (4 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check844 (p : Pattern) : (!pushGuard support p 189 163 137 137 || decide (bonus 189 p ≤ 1 + Generated.soko3_2Potential.boulder 137 - Generated.soko3_2Potential.boulder 163 + bonus 163 (change p 163 (some 137)))) = true :=
  check_of_implication _ _ (bound844 p)
theorem guard845 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 215 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound845 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 215 .south = true) : bonus 189 p ≤ bonus 215 p := by
  have certified := compare0 p (guard845 p guard)
  simpa only [at189, at215, Int.zero_add] using certified
theorem check845 (p : Pattern) : (!walkGuard soko3_2.board support p 189 215 .south || decide (bonus 189 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound845 p)
theorem guard846 (p : Pattern) (guard : pushGuard support p 189 215 241 241 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound846 (p : Pattern) (guard : pushGuard support p 189 215 241 241 = true) : bonus 189 p ≤ 1 + Generated.soko3_2Potential.boulder 241 - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some 241)) := by
  have certified := compare0 p (guard846 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 215 (some 241))
  have normalized := agree134 _ _ (change_representative support p 215 (some 241) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check846 (p : Pattern) : (!pushGuard support p 189 215 241 241 || decide (bonus 189 p ≤ 1 + Generated.soko3_2Potential.boulder 241 - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some 241)))) = true :=
  check_of_implication _ _ (bound846 p)
theorem guard847 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 188 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound847 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 188 .west = true) : bonus 189 p ≤ bonus 188 p := by
  have certified := compare0 p (guard847 p guard)
  simpa only [at189, at188, Int.zero_add] using certified
theorem check847 (p : Pattern) : (!walkGuard soko3_2.board support p 189 188 .west || decide (bonus 189 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound847 p)
theorem guard848 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 162 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound848 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 162 .northWest = true) : bonus 189 p ≤ bonus 162 p := by
  have certified := compare0 p (guard848 p guard)
  simpa only [at189, at162, Int.zero_add] using certified
theorem check848 (p : Pattern) : (!walkGuard soko3_2.board support p 189 162 .northWest || decide (bonus 189 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound848 p)
theorem guard849 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 216 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound849 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 216 .southEast = true) : bonus 189 p ≤ bonus 216 p := by
  have certified := compare0 p (guard849 p guard)
  simpa only [at189, at216, Int.zero_add] using certified
theorem check849 (p : Pattern) : (!walkGuard soko3_2.board support p 189 216 .southEast || decide (bonus 189 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound849 p)
theorem guard850 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 214 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound850 (p : Pattern) (guard : walkGuard soko3_2.board support p 189 214 .southWest = true) : bonus 189 p ≤ bonus 214 p := by
  have certified := compare0 p (guard850 p guard)
  simpa only [at189, at214, Int.zero_add] using certified
theorem check850 (p : Pattern) : (!walkGuard soko3_2.board support p 189 214 .southWest || decide (bonus 189 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound850 p)
theorem guard851 (p : Pattern) (guard : walkGuard soko3_2.board support p 192 166 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound851 (p : Pattern) (guard : walkGuard soko3_2.board support p 192 166 .north = true) : bonus 192 p ≤ bonus 166 p := by
  have certified := compare0 p (guard851 p guard)
  simpa only [at192, at166, Int.zero_add] using certified
theorem check851 (p : Pattern) : (!walkGuard soko3_2.board support p 192 166 .north || decide (bonus 192 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound851 p)
theorem guard852 (p : Pattern) (guard : walkGuard soko3_2.board support p 192 218 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound852 (p : Pattern) (guard : walkGuard soko3_2.board support p 192 218 .south = true) : bonus 192 p ≤ bonus 218 p := by
  have certified := compare0 p (guard852 p guard)
  simpa only [at192, at218, Int.zero_add] using certified
theorem check852 (p : Pattern) : (!walkGuard soko3_2.board support p 192 218 .south || decide (bonus 192 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound852 p)
theorem guard853 (p : Pattern) (guard : pushGuard support p 192 218 244 244 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound853 (p : Pattern) (guard : pushGuard support p 192 218 244 244 = true) : bonus 192 p ≤ 1 + Generated.soko3_2Potential.boulder 244 - Generated.soko3_2Potential.boulder 218 + bonus 218 (change p 218 (some 244)) := by
  have certified := compare0 p (guard853 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 218 (some 244))
  have normalized := agree134 _ _ (change_representative support p 218 (some 244) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check853 (p : Pattern) : (!pushGuard support p 192 218 244 244 || decide (bonus 192 p ≤ 1 + Generated.soko3_2Potential.boulder 244 - Generated.soko3_2Potential.boulder 218 + bonus 218 (change p 218 (some 244)))) = true :=
  check_of_implication _ _ (bound853 p)
theorem guard854 (p : Pattern) (guard : walkGuard soko3_2.board support p 192 165 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound854 (p : Pattern) (guard : walkGuard soko3_2.board support p 192 165 .northWest = true) : bonus 192 p ≤ bonus 165 p := by
  have certified := compare0 p (guard854 p guard)
  simpa only [at192, at165, Int.zero_add] using certified
theorem check854 (p : Pattern) : (!walkGuard soko3_2.board support p 192 165 .northWest || decide (bonus 192 p ≤ bonus 165 p)) = true :=
  check_of_implication _ _ (bound854 p)
theorem guard855 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 172 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound855 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 172 .north = true) : bonus 198 p ≤ bonus 172 p := by
  have certified := compare103 p (guard855 p guard)
  simpa only [at198, at172, Int.zero_add] using certified
theorem check855 (p : Pattern) : (!walkGuard soko3_2.board support p 198 172 .north || decide (bonus 198 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound855 p)
theorem guard856 (p : Pattern) (guard : pushGuard support p 198 172 146 146 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound856 (p : Pattern) (guard : pushGuard support p 198 172 146 146 = true) : bonus 198 p ≤ 1 + Generated.soko3_2Potential.boulder 146 - Generated.soko3_2Potential.boulder 172 + bonus 172 (change p 172 (some 146)) := by
  have certified := compare37 p (guard856 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 172 (some 146))
  have normalized := agree0 _ _ (change_representative support p 172 (some 146) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check856 (p : Pattern) : (!pushGuard support p 198 172 146 146 || decide (bonus 198 p ≤ 1 + Generated.soko3_2Potential.boulder 146 - Generated.soko3_2Potential.boulder 172 + bonus 172 (change p 172 (some 146)))) = true :=
  check_of_implication _ _ (bound856 p)
theorem guard857 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 224 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound857 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 224 .south = true) : bonus 198 p ≤ bonus 224 p := by
  have certified := compare103 p (guard857 p guard)
  simpa only [at198, at224, Int.zero_add] using certified
theorem check857 (p : Pattern) : (!walkGuard soko3_2.board support p 198 224 .south || decide (bonus 198 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound857 p)
theorem guard858 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 199 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound858 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 199 .east = true) : bonus 198 p ≤ bonus 199 p := by
  have certified := compare103 p (guard858 p guard)
  simpa only [at198, at199, Int.zero_add] using certified
theorem check858 (p : Pattern) : (!walkGuard soko3_2.board support p 198 199 .east || decide (bonus 198 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound858 p)
theorem guard859 (p : Pattern) (guard : pushGuard support p 198 199 200 200 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound859 (p : Pattern) (guard : pushGuard support p 198 199 200 200 = true) : bonus 198 p ≤ 1 + Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some 200)) := by
  have certified := compare37 p (guard859 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 199 (some 200))
  have normalized := agree0 _ _ (change_representative support p 199 (some 200) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check859 (p : Pattern) : (!pushGuard support p 198 199 200 200 || decide (bonus 198 p ≤ 1 + Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some 200)))) = true :=
  check_of_implication _ _ (bound859 p)
theorem guard860 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 173 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound860 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 173 .northEast = true) : bonus 198 p ≤ bonus 173 p := by
  have certified := compare103 p (guard860 p guard)
  simpa only [at198, at173, Int.zero_add] using certified
theorem check860 (p : Pattern) : (!walkGuard soko3_2.board support p 198 173 .northEast || decide (bonus 198 p ≤ bonus 173 p)) = true :=
  check_of_implication _ _ (bound860 p)
theorem guard861 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 225 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound861 (p : Pattern) (guard : walkGuard soko3_2.board support p 198 225 .southEast = true) : bonus 198 p ≤ bonus 225 p := by
  have certified := compare103 p (guard861 p guard)
  simpa only [at198, at225, Int.zero_add] using certified
theorem check861 (p : Pattern) : (!walkGuard soko3_2.board support p 198 225 .southEast || decide (bonus 198 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound861 p)
theorem guard862 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 173 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound862 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 173 .north = true) : bonus 199 p ≤ bonus 173 p := by
  have certified := compare103 p (guard862 p guard)
  simpa only [at199, at173, Int.zero_add] using certified
theorem check862 (p : Pattern) : (!walkGuard soko3_2.board support p 199 173 .north || decide (bonus 199 p ≤ bonus 173 p)) = true :=
  check_of_implication _ _ (bound862 p)
theorem guard863 (p : Pattern) (guard : pushGuard support p 199 173 147 147 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound863 (p : Pattern) (guard : pushGuard support p 199 173 147 147 = true) : bonus 199 p ≤ 1 + Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some 147)) := by
  have certified := compare37 p (guard863 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 173 (some 147))
  have normalized := agree0 _ _ (change_representative support p 173 (some 147) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check863 (p : Pattern) : (!pushGuard support p 199 173 147 147 || decide (bonus 199 p ≤ 1 + Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some 147)))) = true :=
  check_of_implication _ _ (bound863 p)
end NetHack.Sokoban32Refined
