import NetHack.Sokoban12CostPartition.ActionBounds030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard744 (p : Pattern) (guard : pushGuard support p 279 280 281 281 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound744 (p : Pattern) (guard : pushGuard support p 279 280 281 281 = true) : bonus 279 p ≤ 1 + Generated.soko1_2Potential.boulder 281 - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some 281)) := by
  have certified := compare1005 p (guard744 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 280 (some 281))
  have normalized := agree0 _ _ (change_representative support p 280 (some 281) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check744 (p : Pattern) : (!pushGuard support p 279 280 281 281 || decide (bonus 279 p ≤ 1 + Generated.soko1_2Potential.boulder 281 - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some 281)))) = true :=
  check_of_implication _ _ (bound744 p)
theorem guard745 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 278 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound745 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 278 .west = true) : bonus 279 p ≤ bonus 278 p := by
  have certified := compare898 p (guard745 p guard)
  simpa only [at279, at278, Int.zero_add] using certified
theorem check745 (p : Pattern) : (!walkGuard soko1_2.board support p 279 278 .west || decide (bonus 279 p ≤ bonus 278 p)) = true :=
  check_of_implication _ _ (bound745 p)
theorem guard746 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 254 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound746 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 254 .northEast = true) : bonus 279 p ≤ bonus 254 p := by
  have certified := compare898 p (guard746 p guard)
  simpa only [at279, at254, Int.zero_add] using certified
theorem check746 (p : Pattern) : (!walkGuard soko1_2.board support p 279 254 .northEast || decide (bonus 279 p ≤ bonus 254 p)) = true :=
  check_of_implication _ _ (bound746 p)
theorem guard747 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 252 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound747 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 252 .northWest = true) : bonus 279 p ≤ bonus 252 p := by
  have certified := compare898 p (guard747 p guard)
  simpa only [at279, at252, Int.zero_add] using certified
theorem check747 (p : Pattern) : (!walkGuard soko1_2.board support p 279 252 .northWest || decide (bonus 279 p ≤ bonus 252 p)) = true :=
  check_of_implication _ _ (bound747 p)
theorem guard748 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 306 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound748 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 306 .southEast = true) : bonus 279 p ≤ bonus 306 p := by
  have certified := compare898 p (guard748 p guard)
  simpa only [at279, at306, Int.zero_add] using certified
theorem check748 (p : Pattern) : (!walkGuard soko1_2.board support p 279 306 .southEast || decide (bonus 279 p ≤ bonus 306 p)) = true :=
  check_of_implication _ _ (bound748 p)
theorem guard749 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 304 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound749 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 304 .southWest = true) : bonus 279 p ≤ bonus 304 p := by
  have certified := compare898 p (guard749 p guard)
  simpa only [at279, at304, Int.zero_add] using certified
theorem check749 (p : Pattern) : (!walkGuard soko1_2.board support p 279 304 .southWest || decide (bonus 279 p ≤ bonus 304 p)) = true :=
  check_of_implication _ _ (bound749 p)
theorem guard750 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 254 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound750 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 254 .north = true) : bonus 280 p ≤ bonus 254 p := by
  have certified := compare898 p (guard750 p guard)
  simpa only [at280, at254, Int.zero_add] using certified
theorem check750 (p : Pattern) : (!walkGuard soko1_2.board support p 280 254 .north || decide (bonus 280 p ≤ bonus 254 p)) = true :=
  check_of_implication _ _ (bound750 p)
theorem guard751 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 306 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound751 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 306 .south = true) : bonus 280 p ≤ bonus 306 p := by
  have certified := compare898 p (guard751 p guard)
  simpa only [at280, at306, Int.zero_add] using certified
theorem check751 (p : Pattern) : (!walkGuard soko1_2.board support p 280 306 .south || decide (bonus 280 p ≤ bonus 306 p)) = true :=
  check_of_implication _ _ (bound751 p)
theorem guard752 (p : Pattern) (guard : pushGuard support p 280 306 332 332 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound752 (p : Pattern) (guard : pushGuard support p 280 306 332 332 = true) : bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some 332)) := by
  have certified := compare1005 p (guard752 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 306 (some 332))
  have normalized := agree0 _ _ (change_representative support p 306 (some 332) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check752 (p : Pattern) : (!pushGuard support p 280 306 332 332 || decide (bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some 332)))) = true :=
  check_of_implication _ _ (bound752 p)
theorem guard753 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 281 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound753 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 281 .east = true) : bonus 280 p ≤ bonus 281 p := by
  have certified := compare898 p (guard753 p guard)
  simpa only [at280, at281, Int.zero_add] using certified
theorem check753 (p : Pattern) : (!walkGuard soko1_2.board support p 280 281 .east || decide (bonus 280 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound753 p)
theorem guard754 (p : Pattern) (guard : pushGuard support p 280 281 282 282 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound754 (p : Pattern) (guard : pushGuard support p 280 281 282 282 = true) : bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder 282 - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some 282)) := by
  have certified := compare1005 p (guard754 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 281 (some 282))
  have normalized := agree0 _ _ (change_representative support p 281 (some 282) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check754 (p : Pattern) : (!pushGuard support p 280 281 282 282 || decide (bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder 282 - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some 282)))) = true :=
  check_of_implication _ _ (bound754 p)
theorem guard755 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 279 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound755 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 279 .west = true) : bonus 280 p ≤ bonus 279 p := by
  have certified := compare898 p (guard755 p guard)
  simpa only [at280, at279, Int.zero_add] using certified
theorem check755 (p : Pattern) : (!walkGuard soko1_2.board support p 280 279 .west || decide (bonus 280 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound755 p)
theorem guard756 (p : Pattern) (guard : pushGuard support p 280 279 278 278 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound756 (p : Pattern) (guard : pushGuard support p 280 279 278 278 = true) : bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder 278 - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some 278)) := by
  have certified := compare1005 p (guard756 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 279 (some 278))
  have normalized := agree0 _ _ (change_representative support p 279 (some 278) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check756 (p : Pattern) : (!pushGuard support p 280 279 278 278 || decide (bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder 278 - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some 278)))) = true :=
  check_of_implication _ _ (bound756 p)
theorem guard757 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 255 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound757 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 255 .northEast = true) : bonus 280 p ≤ bonus 255 p := by
  have certified := compare898 p (guard757 p guard)
  simpa only [at280, at255, Int.zero_add] using certified
theorem check757 (p : Pattern) : (!walkGuard soko1_2.board support p 280 255 .northEast || decide (bonus 280 p ≤ bonus 255 p)) = true :=
  check_of_implication _ _ (bound757 p)
theorem guard758 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 253 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound758 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 253 .northWest = true) : bonus 280 p ≤ bonus 253 p := by
  have certified := compare898 p (guard758 p guard)
  simpa only [at280, at253, Int.zero_add] using certified
theorem check758 (p : Pattern) : (!walkGuard soko1_2.board support p 280 253 .northWest || decide (bonus 280 p ≤ bonus 253 p)) = true :=
  check_of_implication _ _ (bound758 p)
theorem guard759 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 307 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound759 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 307 .southEast = true) : bonus 280 p ≤ bonus 307 p := by
  have certified := compare898 p (guard759 p guard)
  simpa only [at280, at307, Int.zero_add] using certified
theorem check759 (p : Pattern) : (!walkGuard soko1_2.board support p 280 307 .southEast || decide (bonus 280 p ≤ bonus 307 p)) = true :=
  check_of_implication _ _ (bound759 p)
theorem guard760 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 305 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound760 (p : Pattern) (guard : walkGuard soko1_2.board support p 280 305 .southWest = true) : bonus 280 p ≤ bonus 305 p := by
  have certified := compare898 p (guard760 p guard)
  simpa only [at280, at305, Int.zero_add] using certified
theorem check760 (p : Pattern) : (!walkGuard soko1_2.board support p 280 305 .southWest || decide (bonus 280 p ≤ bonus 305 p)) = true :=
  check_of_implication _ _ (bound760 p)
theorem guard761 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 255 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound761 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 255 .north = true) : bonus 281 p ≤ bonus 255 p := by
  have certified := compare898 p (guard761 p guard)
  simpa only [at281, at255, Int.zero_add] using certified
theorem check761 (p : Pattern) : (!walkGuard soko1_2.board support p 281 255 .north || decide (bonus 281 p ≤ bonus 255 p)) = true :=
  check_of_implication _ _ (bound761 p)
theorem guard762 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 307 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound762 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 307 .south = true) : bonus 281 p ≤ bonus 307 p := by
  have certified := compare898 p (guard762 p guard)
  simpa only [at281, at307, Int.zero_add] using certified
theorem check762 (p : Pattern) : (!walkGuard soko1_2.board support p 281 307 .south || decide (bonus 281 p ≤ bonus 307 p)) = true :=
  check_of_implication _ _ (bound762 p)
theorem guard763 (p : Pattern) (guard : pushGuard support p 281 307 333 333 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound763 (p : Pattern) (guard : pushGuard support p 281 307 333 333 = true) : bonus 281 p ≤ 1 + Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some 333)) := by
  have certified := compare1005 p (guard763 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 307 (some 333))
  have normalized := agree0 _ _ (change_representative support p 307 (some 333) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check763 (p : Pattern) : (!pushGuard support p 281 307 333 333 || decide (bonus 281 p ≤ 1 + Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some 333)))) = true :=
  check_of_implication _ _ (bound763 p)
theorem guard764 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 282 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound764 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 282 .east = true) : bonus 281 p ≤ bonus 282 p := by
  have certified := compare898 p (guard764 p guard)
  simpa only [at281, at282, Int.zero_add] using certified
theorem check764 (p : Pattern) : (!walkGuard soko1_2.board support p 281 282 .east || decide (bonus 281 p ≤ bonus 282 p)) = true :=
  check_of_implication _ _ (bound764 p)
theorem guard765 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 280 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound765 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 280 .west = true) : bonus 281 p ≤ bonus 280 p := by
  have certified := compare898 p (guard765 p guard)
  simpa only [at281, at280, Int.zero_add] using certified
theorem check765 (p : Pattern) : (!walkGuard soko1_2.board support p 281 280 .west || decide (bonus 281 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound765 p)
theorem guard766 (p : Pattern) (guard : pushGuard support p 281 280 279 279 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound766 (p : Pattern) (guard : pushGuard support p 281 280 279 279 = true) : bonus 281 p ≤ 1 + Generated.soko1_2Potential.boulder 279 - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some 279)) := by
  have certified := compare1005 p (guard766 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 280 (some 279))
  have normalized := agree0 _ _ (change_representative support p 280 (some 279) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check766 (p : Pattern) : (!pushGuard support p 281 280 279 279 || decide (bonus 281 p ≤ 1 + Generated.soko1_2Potential.boulder 279 - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some 279)))) = true :=
  check_of_implication _ _ (bound766 p)
theorem guard767 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 256 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound767 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 256 .northEast = true) : bonus 281 p ≤ bonus 256 p := by
  have certified := compare898 p (guard767 p guard)
  simpa only [at281, at256, Int.zero_add] using certified
theorem check767 (p : Pattern) : (!walkGuard soko1_2.board support p 281 256 .northEast || decide (bonus 281 p ≤ bonus 256 p)) = true :=
  check_of_implication _ _ (bound767 p)
end NetHack.Sokoban12CostPartition
