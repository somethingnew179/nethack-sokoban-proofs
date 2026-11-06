import NetHack.Sokoban12CostPartition.ActionBounds033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard816 (p : Pattern) (guard : pushGuard support p 292 291 290 290 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound816 (p : Pattern) (guard : pushGuard support p 292 291 290 290 = true) : bonus 292 p ≤ 1 + Generated.soko1_2Potential.boulder 290 - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some 290)) := by
  have certified := compare2570 p (guard816 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 291 (some 290))
  have normalized := agree258 _ _ (change_representative support p 291 (some 290) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check816 (p : Pattern) : (!pushGuard support p 292 291 290 290 || decide (bonus 292 p ≤ 1 + Generated.soko1_2Potential.boulder 290 - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some 290)))) = true :=
  check_of_implication _ _ (bound816 p)
theorem guard817 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 265 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound817 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 265 .northWest = true) : bonus 292 p ≤ bonus 265 p := by
  have certified := compare897 p (guard817 p guard)
  simpa only [at292, at265, Int.zero_add] using certified
theorem check817 (p : Pattern) : (!walkGuard soko1_2.board support p 292 265 .northWest || decide (bonus 292 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound817 p)
theorem guard818 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 319 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound818 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 319 .southEast = true) : bonus 292 p ≤ bonus 319 p := by
  have certified := compare897 p (guard818 p guard)
  simpa only [at292, at319, Int.zero_add] using certified
theorem check818 (p : Pattern) : (!walkGuard soko1_2.board support p 292 319 .southEast || decide (bonus 292 p ≤ bonus 319 p)) = true :=
  check_of_implication _ _ (bound818 p)
theorem guard819 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 317 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound819 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 317 .southWest = true) : bonus 292 p ≤ bonus 317 p := by
  have certified := compare897 p (guard819 p guard)
  simpa only [at292, at317, Int.zero_add] using certified
theorem check819 (p : Pattern) : (!walkGuard soko1_2.board support p 292 317 .southWest || decide (bonus 292 p ≤ bonus 317 p)) = true :=
  check_of_implication _ _ (bound819 p)
theorem guard820 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 319 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound820 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 319 .south = true) : bonus 293 p ≤ bonus 319 p := by
  have certified := compare897 p (guard820 p guard)
  simpa only [at293, at319, Int.zero_add] using certified
theorem check820 (p : Pattern) : (!walkGuard soko1_2.board support p 293 319 .south || decide (bonus 293 p ≤ bonus 319 p)) = true :=
  check_of_implication _ _ (bound820 p)
theorem guard821 (p : Pattern) (guard : pushGuard support p 293 319 345 345 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound821 (p : Pattern) (guard : pushGuard support p 293 319 345 345 = true) : bonus 293 p ≤ 1 + Generated.soko1_2Potential.boulder 345 - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some 345)) := by
  have certified := compare2570 p (guard821 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 319 (some 345))
  have normalized := agree258 _ _ (change_representative support p 319 (some 345) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check821 (p : Pattern) : (!pushGuard support p 293 319 345 345 || decide (bonus 293 p ≤ 1 + Generated.soko1_2Potential.boulder 345 - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some 345)))) = true :=
  check_of_implication _ _ (bound821 p)
theorem guard822 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 294 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound822 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 294 .east = true) : bonus 293 p ≤ bonus 294 p := by
  have certified := compare897 p (guard822 p guard)
  simpa only [at293, at294, Int.zero_add] using certified
theorem check822 (p : Pattern) : (!walkGuard soko1_2.board support p 293 294 .east || decide (bonus 293 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound822 p)
theorem guard823 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 292 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound823 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 292 .west = true) : bonus 293 p ≤ bonus 292 p := by
  have certified := compare897 p (guard823 p guard)
  simpa only [at293, at292, Int.zero_add] using certified
theorem check823 (p : Pattern) : (!walkGuard soko1_2.board support p 293 292 .west || decide (bonus 293 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound823 p)
theorem guard824 (p : Pattern) (guard : pushGuard support p 293 292 291 291 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound824 (p : Pattern) (guard : pushGuard support p 293 292 291 291 = true) : bonus 293 p ≤ 1 + Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.boulder 292 + bonus 292 (change p 292 (some 291)) := by
  have certified := compare897 p (guard824 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 292 (some 291))
  have normalized := agree258 _ _ (change_representative support p 292 (some 291) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check824 (p : Pattern) : (!pushGuard support p 293 292 291 291 || decide (bonus 293 p ≤ 1 + Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.boulder 292 + bonus 292 (change p 292 (some 291)))) = true :=
  check_of_implication _ _ (bound824 p)
theorem guard825 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 320 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound825 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 320 .southEast = true) : bonus 293 p ≤ bonus 320 p := by
  have certified := compare897 p (guard825 p guard)
  simpa only [at293, at320, Int.zero_add] using certified
theorem check825 (p : Pattern) : (!walkGuard soko1_2.board support p 293 320 .southEast || decide (bonus 293 p ≤ bonus 320 p)) = true :=
  check_of_implication _ _ (bound825 p)
theorem guard826 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 318 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound826 (p : Pattern) (guard : walkGuard soko1_2.board support p 293 318 .southWest = true) : bonus 293 p ≤ bonus 318 p := by
  have certified := compare897 p (guard826 p guard)
  simpa only [at293, at318, Int.zero_add] using certified
theorem check826 (p : Pattern) : (!walkGuard soko1_2.board support p 293 318 .southWest || decide (bonus 293 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound826 p)
theorem guard827 (p : Pattern) (guard : walkGuard soko1_2.board support p 294 320 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound827 (p : Pattern) (guard : walkGuard soko1_2.board support p 294 320 .south = true) : bonus 294 p ≤ bonus 320 p := by
  have certified := compare897 p (guard827 p guard)
  simpa only [at294, at320, Int.zero_add] using certified
theorem check827 (p : Pattern) : (!walkGuard soko1_2.board support p 294 320 .south || decide (bonus 294 p ≤ bonus 320 p)) = true :=
  check_of_implication _ _ (bound827 p)
theorem guard828 (p : Pattern) (guard : walkGuard soko1_2.board support p 294 293 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound828 (p : Pattern) (guard : walkGuard soko1_2.board support p 294 293 .west = true) : bonus 294 p ≤ bonus 293 p := by
  have certified := compare897 p (guard828 p guard)
  simpa only [at294, at293, Int.zero_add] using certified
theorem check828 (p : Pattern) : (!walkGuard soko1_2.board support p 294 293 .west || decide (bonus 294 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound828 p)
theorem guard829 (p : Pattern) (guard : pushGuard support p 294 293 292 292 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound829 (p : Pattern) (guard : pushGuard support p 294 293 292 292 = true) : bonus 294 p ≤ 1 + Generated.soko1_2Potential.boulder 292 - Generated.soko1_2Potential.boulder 293 + bonus 293 (change p 293 (some 292)) := by
  have certified := compare897 p (guard829 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 293 (some 292))
  have normalized := agree258 _ _ (change_representative support p 293 (some 292) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check829 (p : Pattern) : (!pushGuard support p 294 293 292 292 || decide (bonus 294 p ≤ 1 + Generated.soko1_2Potential.boulder 292 - Generated.soko1_2Potential.boulder 293 + bonus 293 (change p 293 (some 292)))) = true :=
  check_of_implication _ _ (bound829 p)
theorem guard830 (p : Pattern) (guard : walkGuard soko1_2.board support p 294 319 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound830 (p : Pattern) (guard : walkGuard soko1_2.board support p 294 319 .southWest = true) : bonus 294 p ≤ bonus 319 p := by
  have certified := compare897 p (guard830 p guard)
  simpa only [at294, at319, Int.zero_add] using certified
theorem check830 (p : Pattern) : (!walkGuard soko1_2.board support p 294 319 .southWest || decide (bonus 294 p ≤ bonus 319 p)) = true :=
  check_of_implication _ _ (bound830 p)
theorem guard831 (p : Pattern) (guard : walkGuard soko1_2.board support p 296 270 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound831 (p : Pattern) (guard : walkGuard soko1_2.board support p 296 270 .north = true) : bonus 296 p ≤ bonus 270 p := by
  have certified := compare897 p (guard831 p guard)
  simpa only [at296, at270, Int.zero_add] using certified
theorem check831 (p : Pattern) : (!walkGuard soko1_2.board support p 296 270 .north || decide (bonus 296 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound831 p)
theorem guard832 (p : Pattern) (guard : pushGuard support p 296 270 244 244 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound832 (p : Pattern) (guard : pushGuard support p 296 270 244 244 = true) : bonus 296 p ≤ 1 + Generated.soko1_2Potential.boulder 244 - Generated.soko1_2Potential.boulder 270 + bonus 270 (change p 270 (some 244)) := by
  have certified := compare897 p (guard832 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 270 (some 244))
  have normalized := agree258 _ _ (change_representative support p 270 (some 244) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check832 (p : Pattern) : (!pushGuard support p 296 270 244 244 || decide (bonus 296 p ≤ 1 + Generated.soko1_2Potential.boulder 244 - Generated.soko1_2Potential.boulder 270 + bonus 270 (change p 270 (some 244)))) = true :=
  check_of_implication _ _ (bound832 p)
theorem guard833 (p : Pattern) (guard : walkGuard soko1_2.board support p 296 322 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound833 (p : Pattern) (guard : walkGuard soko1_2.board support p 296 322 .south = true) : bonus 296 p ≤ bonus 322 p := by
  have certified := compare897 p (guard833 p guard)
  simpa only [at296, at322, Int.zero_add] using certified
theorem check833 (p : Pattern) : (!walkGuard soko1_2.board support p 296 322 .south || decide (bonus 296 p ≤ bonus 322 p)) = true :=
  check_of_implication _ _ (bound833 p)
theorem guard834 (p : Pattern) (guard : pushGuard support p 296 322 348 348 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound834 (p : Pattern) (guard : pushGuard support p 296 322 348 348 = true) : bonus 296 p ≤ 1 + Generated.soko1_2Potential.boulder 348 - Generated.soko1_2Potential.boulder 322 + bonus 322 (change p 322 (some 348)) := by
  have certified := compare5431 p (guard834 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 322 (some 348))
  have normalized := agree258 _ _ (change_representative support p 322 (some 348) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check834 (p : Pattern) : (!pushGuard support p 296 322 348 348 || decide (bonus 296 p ≤ 1 + Generated.soko1_2Potential.boulder 348 - Generated.soko1_2Potential.boulder 322 + bonus 322 (change p 322 (some 348)))) = true :=
  check_of_implication _ _ (bound834 p)
theorem guard835 (p : Pattern) (guard : walkGuard soko1_2.board support p 296 297 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound835 (p : Pattern) (guard : walkGuard soko1_2.board support p 296 297 .east = true) : bonus 296 p ≤ bonus 297 p := by
  have certified := compare897 p (guard835 p guard)
  simpa only [at296, at297, Int.zero_add] using certified
theorem check835 (p : Pattern) : (!walkGuard soko1_2.board support p 296 297 .east || decide (bonus 296 p ≤ bonus 297 p)) = true :=
  check_of_implication _ _ (bound835 p)
theorem guard836 (p : Pattern) (guard : walkGuard soko1_2.board support p 296 271 .northEast = true) : d1233 p = 1 := by
  change (!false && !(p 271) && !(true && false && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound836 (p : Pattern) (guard : walkGuard soko1_2.board support p 296 271 .northEast = true) : bonus 296 p ≤ bonus 271 p := by
  have certified := compare6080 p (guard836 p guard)
  simpa only [at296, at271, Int.zero_add] using certified
theorem check836 (p : Pattern) : (!walkGuard soko1_2.board support p 296 271 .northEast || decide (bonus 296 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound836 p)
theorem guard837 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 271 .north = true) : d1233 p = 1 := by
  change (!false && !(p 271) && !false) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound837 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 271 .north = true) : bonus 297 p ≤ bonus 271 p := by
  have certified := compare6080 p (guard837 p guard)
  simpa only [at297, at271, Int.zero_add] using certified
theorem check837 (p : Pattern) : (!walkGuard soko1_2.board support p 297 271 .north || decide (bonus 297 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound837 p)
theorem guard838 (p : Pattern) (guard : pushGuard support p 297 271 245 245 = true) : d8 p = 1 := by
  change (!false && (!true || (p 271)) && !false && (!false || false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d8, h271] at guard ⊢
theorem bound838 (p : Pattern) (guard : pushGuard support p 297 271 245 245 = true) : bonus 297 p ≤ 1 + Generated.soko1_2Potential.boulder 245 - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some 245)) := by
  have certified := compare6196 p (guard838 p guard)
  change d258 p ≤ (1 : Int) + d733 (change p 271 (some 245))
  have normalized := agree733 _ _ (change_representative support p 271 (some 245) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d733 (change p 271 none)
  rw [sub2702]
  exact certified
theorem check838 (p : Pattern) : (!pushGuard support p 297 271 245 245 || decide (bonus 297 p ≤ 1 + Generated.soko1_2Potential.boulder 245 - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some 245)))) = true :=
  check_of_implication _ _ (bound838 p)
theorem guard839 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 296 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound839 (p : Pattern) (guard : walkGuard soko1_2.board support p 297 296 .west = true) : bonus 297 p ≤ bonus 296 p := by
  have certified := compare897 p (guard839 p guard)
  simpa only [at297, at296, Int.zero_add] using certified
theorem check839 (p : Pattern) : (!walkGuard soko1_2.board support p 297 296 .west || decide (bonus 297 p ≤ bonus 296 p)) = true :=
  check_of_implication _ _ (bound839 p)
end NetHack.Sokoban12CostPartition
