import NetHack.Sokoban12CostPartition.ActionBounds034
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard840 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 272 .northEast = true) : d1233 p = 1 := by
  change (!false && !false && !(true && (p 271) && true)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound840 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 272 .northEast = true) : bonus 297 p ≤ bonus 272 p := by
  have certified := compare6291 p (guard840 p guard)
  simpa only [at297, at272, Int.zero_add] using certified
theorem check840 (p : Pattern) : (!walkGuard soko1_2.board support p 297 272 .northEast || decide (bonus 297 p ≤ bonus 272 p)) = true :=
  check_of_implication _ _ (bound840 p)
theorem guard841 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 270 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 271) && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d1, h271] at guard ⊢
theorem bound841 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 270 .northWest = true) : bonus 297 p ≤ bonus 270 p := by
  have certified := compare897 p (guard841 p guard)
  simpa only [at297, at270, Int.zero_add] using certified
theorem check841 (p : Pattern) : (!walkGuard soko1_2.board support p 297 270 .northWest || decide (bonus 297 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound841 p)
theorem guard842 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 322 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound842 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 322 .southWest = true) : bonus 297 p ≤ bonus 322 p := by
  have certified := compare897 p (guard842 p guard)
  simpa only [at297, at322, Int.zero_add] using certified
theorem check842 (p : Pattern) : (!walkGuard soko1_2.board support p 297 322 .southWest || decide (bonus 297 p ≤ bonus 322 p)) = true :=
  check_of_implication _ _ (bound842 p)
theorem guard843 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 278 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound843 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 278 .north = true) : bonus 304 p ≤ bonus 278 p := by
  have certified := compare898 p (guard843 p guard)
  simpa only [at304, at278, Int.zero_add] using certified
theorem check843 (p : Pattern) : (!walkGuard soko1_2.board support p 304 278 .north || decide (bonus 304 p ≤ bonus 278 p)) = true :=
  check_of_implication _ _ (bound843 p)
theorem guard844 (p : Pattern) (guard : pushGuard support p 304 278 252 252 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound844 (p : Pattern) (guard : pushGuard support p 304 278 252 252 = true) : bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder 252 - Generated.soko1_2Potential.boulder 278 + bonus 278 (change p 278 (some 252)) := by
  have certified := compare1005 p (guard844 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 278 (some 252))
  have normalized := agree0 _ _ (change_representative support p 278 (some 252) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check844 (p : Pattern) : (!pushGuard support p 304 278 252 252 || decide (bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder 252 - Generated.soko1_2Potential.boulder 278 + bonus 278 (change p 278 (some 252)))) = true :=
  check_of_implication _ _ (bound844 p)
theorem guard845 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 330 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound845 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 330 .south = true) : bonus 304 p ≤ bonus 330 p := by
  have certified := compare898 p (guard845 p guard)
  simpa only [at304, at330, Int.zero_add] using certified
theorem check845 (p : Pattern) : (!walkGuard soko1_2.board support p 304 330 .south || decide (bonus 304 p ≤ bonus 330 p)) = true :=
  check_of_implication _ _ (bound845 p)
theorem guard846 (p : Pattern) (guard : pushGuard support p 304 330 356 356 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound846 (p : Pattern) (guard : pushGuard support p 304 330 356 356 = true) : bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder 356 - Generated.soko1_2Potential.boulder 330 + bonus 330 (change p 330 (some 356)) := by
  have certified := compare1005 p (guard846 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 330 (some 356))
  have normalized := agree0 _ _ (change_representative support p 330 (some 356) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check846 (p : Pattern) : (!pushGuard support p 304 330 356 356 || decide (bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder 356 - Generated.soko1_2Potential.boulder 330 + bonus 330 (change p 330 (some 356)))) = true :=
  check_of_implication _ _ (bound846 p)
theorem guard847 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 305 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound847 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 305 .east = true) : bonus 304 p ≤ bonus 305 p := by
  have certified := compare898 p (guard847 p guard)
  simpa only [at304, at305, Int.zero_add] using certified
theorem check847 (p : Pattern) : (!walkGuard soko1_2.board support p 304 305 .east || decide (bonus 304 p ≤ bonus 305 p)) = true :=
  check_of_implication _ _ (bound847 p)
theorem guard848 (p : Pattern) (guard : pushGuard support p 304 305 306 306 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound848 (p : Pattern) (guard : pushGuard support p 304 305 306 306 = true) : bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some 306)) := by
  have certified := compare1005 p (guard848 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 305 (some 306))
  have normalized := agree0 _ _ (change_representative support p 305 (some 306) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check848 (p : Pattern) : (!pushGuard support p 304 305 306 306 || decide (bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some 306)))) = true :=
  check_of_implication _ _ (bound848 p)
theorem guard849 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 279 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound849 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 279 .northEast = true) : bonus 304 p ≤ bonus 279 p := by
  have certified := compare898 p (guard849 p guard)
  simpa only [at304, at279, Int.zero_add] using certified
theorem check849 (p : Pattern) : (!walkGuard soko1_2.board support p 304 279 .northEast || decide (bonus 304 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound849 p)
theorem guard850 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 331 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound850 (p : Pattern) (guard : walkGuard soko1_2.board support p 304 331 .southEast = true) : bonus 304 p ≤ bonus 331 p := by
  have certified := compare898 p (guard850 p guard)
  simpa only [at304, at331, Int.zero_add] using certified
theorem check850 (p : Pattern) : (!walkGuard soko1_2.board support p 304 331 .southEast || decide (bonus 304 p ≤ bonus 331 p)) = true :=
  check_of_implication _ _ (bound850 p)
theorem guard851 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 279 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound851 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 279 .north = true) : bonus 305 p ≤ bonus 279 p := by
  have certified := compare898 p (guard851 p guard)
  simpa only [at305, at279, Int.zero_add] using certified
theorem check851 (p : Pattern) : (!walkGuard soko1_2.board support p 305 279 .north || decide (bonus 305 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound851 p)
theorem guard852 (p : Pattern) (guard : pushGuard support p 305 279 253 253 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound852 (p : Pattern) (guard : pushGuard support p 305 279 253 253 = true) : bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder 253 - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some 253)) := by
  have certified := compare1005 p (guard852 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 279 (some 253))
  have normalized := agree0 _ _ (change_representative support p 279 (some 253) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check852 (p : Pattern) : (!pushGuard support p 305 279 253 253 || decide (bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder 253 - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some 253)))) = true :=
  check_of_implication _ _ (bound852 p)
theorem guard853 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 331 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound853 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 331 .south = true) : bonus 305 p ≤ bonus 331 p := by
  have certified := compare898 p (guard853 p guard)
  simpa only [at305, at331, Int.zero_add] using certified
theorem check853 (p : Pattern) : (!walkGuard soko1_2.board support p 305 331 .south || decide (bonus 305 p ≤ bonus 331 p)) = true :=
  check_of_implication _ _ (bound853 p)
theorem guard854 (p : Pattern) (guard : pushGuard support p 305 331 357 357 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound854 (p : Pattern) (guard : pushGuard support p 305 331 357 357 = true) : bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some 357)) := by
  have certified := compare1005 p (guard854 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 331 (some 357))
  have normalized := agree0 _ _ (change_representative support p 331 (some 357) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check854 (p : Pattern) : (!pushGuard support p 305 331 357 357 || decide (bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some 357)))) = true :=
  check_of_implication _ _ (bound854 p)
theorem guard855 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 306 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound855 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 306 .east = true) : bonus 305 p ≤ bonus 306 p := by
  have certified := compare898 p (guard855 p guard)
  simpa only [at305, at306, Int.zero_add] using certified
theorem check855 (p : Pattern) : (!walkGuard soko1_2.board support p 305 306 .east || decide (bonus 305 p ≤ bonus 306 p)) = true :=
  check_of_implication _ _ (bound855 p)
theorem guard856 (p : Pattern) (guard : pushGuard support p 305 306 307 307 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound856 (p : Pattern) (guard : pushGuard support p 305 306 307 307 = true) : bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some 307)) := by
  have certified := compare1005 p (guard856 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 306 (some 307))
  have normalized := agree0 _ _ (change_representative support p 306 (some 307) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check856 (p : Pattern) : (!pushGuard support p 305 306 307 307 || decide (bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some 307)))) = true :=
  check_of_implication _ _ (bound856 p)
theorem guard857 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 304 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound857 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 304 .west = true) : bonus 305 p ≤ bonus 304 p := by
  have certified := compare898 p (guard857 p guard)
  simpa only [at305, at304, Int.zero_add] using certified
theorem check857 (p : Pattern) : (!walkGuard soko1_2.board support p 305 304 .west || decide (bonus 305 p ≤ bonus 304 p)) = true :=
  check_of_implication _ _ (bound857 p)
theorem guard858 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 280 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound858 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 280 .northEast = true) : bonus 305 p ≤ bonus 280 p := by
  have certified := compare898 p (guard858 p guard)
  simpa only [at305, at280, Int.zero_add] using certified
theorem check858 (p : Pattern) : (!walkGuard soko1_2.board support p 305 280 .northEast || decide (bonus 305 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound858 p)
theorem guard859 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 278 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound859 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 278 .northWest = true) : bonus 305 p ≤ bonus 278 p := by
  have certified := compare898 p (guard859 p guard)
  simpa only [at305, at278, Int.zero_add] using certified
theorem check859 (p : Pattern) : (!walkGuard soko1_2.board support p 305 278 .northWest || decide (bonus 305 p ≤ bonus 278 p)) = true :=
  check_of_implication _ _ (bound859 p)
theorem guard860 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 332 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound860 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 332 .southEast = true) : bonus 305 p ≤ bonus 332 p := by
  have certified := compare898 p (guard860 p guard)
  simpa only [at305, at332, Int.zero_add] using certified
theorem check860 (p : Pattern) : (!walkGuard soko1_2.board support p 305 332 .southEast || decide (bonus 305 p ≤ bonus 332 p)) = true :=
  check_of_implication _ _ (bound860 p)
theorem guard861 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 330 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound861 (p : Pattern) (guard : walkGuard soko1_2.board support p 305 330 .southWest = true) : bonus 305 p ≤ bonus 330 p := by
  have certified := compare898 p (guard861 p guard)
  simpa only [at305, at330, Int.zero_add] using certified
theorem check861 (p : Pattern) : (!walkGuard soko1_2.board support p 305 330 .southWest || decide (bonus 305 p ≤ bonus 330 p)) = true :=
  check_of_implication _ _ (bound861 p)
theorem guard862 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 280 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound862 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 280 .north = true) : bonus 306 p ≤ bonus 280 p := by
  have certified := compare898 p (guard862 p guard)
  simpa only [at306, at280, Int.zero_add] using certified
theorem check862 (p : Pattern) : (!walkGuard soko1_2.board support p 306 280 .north || decide (bonus 306 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound862 p)
theorem guard863 (p : Pattern) (guard : pushGuard support p 306 280 254 254 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound863 (p : Pattern) (guard : pushGuard support p 306 280 254 254 = true) : bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder 254 - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some 254)) := by
  have certified := compare1005 p (guard863 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 280 (some 254))
  have normalized := agree0 _ _ (change_representative support p 280 (some 254) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check863 (p : Pattern) : (!pushGuard support p 306 280 254 254 || decide (bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder 254 - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some 254)))) = true :=
  check_of_implication _ _ (bound863 p)
end NetHack.Sokoban12CostPartition
