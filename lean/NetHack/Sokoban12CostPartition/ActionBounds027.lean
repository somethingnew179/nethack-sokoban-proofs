import NetHack.Sokoban12CostPartition.ActionBounds026
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard648 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 252 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound648 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 252 .west = true) : bonus 253 p ≤ bonus 252 p := by
  have certified := compare898 p (guard648 p guard)
  simpa only [at253, at252, Int.zero_add] using certified
theorem check648 (p : Pattern) : (!walkGuard soko1_2.board support p 253 252 .west || decide (bonus 253 p ≤ bonus 252 p)) = true :=
  check_of_implication _ _ (bound648 p)
theorem guard649 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 280 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound649 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 280 .southEast = true) : bonus 253 p ≤ bonus 280 p := by
  have certified := compare898 p (guard649 p guard)
  simpa only [at253, at280, Int.zero_add] using certified
theorem check649 (p : Pattern) : (!walkGuard soko1_2.board support p 253 280 .southEast || decide (bonus 253 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound649 p)
theorem guard650 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 278 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound650 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 278 .southWest = true) : bonus 253 p ≤ bonus 278 p := by
  have certified := compare898 p (guard650 p guard)
  simpa only [at253, at278, Int.zero_add] using certified
theorem check650 (p : Pattern) : (!walkGuard soko1_2.board support p 253 278 .southWest || decide (bonus 253 p ≤ bonus 278 p)) = true :=
  check_of_implication _ _ (bound650 p)
theorem guard651 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 280 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound651 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 280 .south = true) : bonus 254 p ≤ bonus 280 p := by
  have certified := compare898 p (guard651 p guard)
  simpa only [at254, at280, Int.zero_add] using certified
theorem check651 (p : Pattern) : (!walkGuard soko1_2.board support p 254 280 .south || decide (bonus 254 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound651 p)
theorem guard652 (p : Pattern) (guard : pushGuard support p 254 280 306 306 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound652 (p : Pattern) (guard : pushGuard support p 254 280 306 306 = true) : bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some 306)) := by
  have certified := compare1005 p (guard652 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 280 (some 306))
  have normalized := agree0 _ _ (change_representative support p 280 (some 306) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check652 (p : Pattern) : (!pushGuard support p 254 280 306 306 || decide (bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some 306)))) = true :=
  check_of_implication _ _ (bound652 p)
theorem guard653 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 255 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound653 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 255 .east = true) : bonus 254 p ≤ bonus 255 p := by
  have certified := compare898 p (guard653 p guard)
  simpa only [at254, at255, Int.zero_add] using certified
theorem check653 (p : Pattern) : (!walkGuard soko1_2.board support p 254 255 .east || decide (bonus 254 p ≤ bonus 255 p)) = true :=
  check_of_implication _ _ (bound653 p)
theorem guard654 (p : Pattern) (guard : pushGuard support p 254 255 256 256 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound654 (p : Pattern) (guard : pushGuard support p 254 255 256 256 = true) : bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder 256 - Generated.soko1_2Potential.boulder 255 + bonus 255 (change p 255 (some 256)) := by
  have certified := compare1005 p (guard654 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 255 (some 256))
  have normalized := agree0 _ _ (change_representative support p 255 (some 256) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check654 (p : Pattern) : (!pushGuard support p 254 255 256 256 || decide (bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder 256 - Generated.soko1_2Potential.boulder 255 + bonus 255 (change p 255 (some 256)))) = true :=
  check_of_implication _ _ (bound654 p)
theorem guard655 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 253 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound655 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 253 .west = true) : bonus 254 p ≤ bonus 253 p := by
  have certified := compare898 p (guard655 p guard)
  simpa only [at254, at253, Int.zero_add] using certified
theorem check655 (p : Pattern) : (!walkGuard soko1_2.board support p 254 253 .west || decide (bonus 254 p ≤ bonus 253 p)) = true :=
  check_of_implication _ _ (bound655 p)
theorem guard656 (p : Pattern) (guard : pushGuard support p 254 253 252 252 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound656 (p : Pattern) (guard : pushGuard support p 254 253 252 252 = true) : bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder 252 - Generated.soko1_2Potential.boulder 253 + bonus 253 (change p 253 (some 252)) := by
  have certified := compare1005 p (guard656 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 253 (some 252))
  have normalized := agree0 _ _ (change_representative support p 253 (some 252) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check656 (p : Pattern) : (!pushGuard support p 254 253 252 252 || decide (bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder 252 - Generated.soko1_2Potential.boulder 253 + bonus 253 (change p 253 (some 252)))) = true :=
  check_of_implication _ _ (bound656 p)
theorem guard657 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 281 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound657 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 281 .southEast = true) : bonus 254 p ≤ bonus 281 p := by
  have certified := compare898 p (guard657 p guard)
  simpa only [at254, at281, Int.zero_add] using certified
theorem check657 (p : Pattern) : (!walkGuard soko1_2.board support p 254 281 .southEast || decide (bonus 254 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound657 p)
theorem guard658 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 279 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound658 (p : Pattern) (guard : walkGuard soko1_2.board support p 254 279 .southWest = true) : bonus 254 p ≤ bonus 279 p := by
  have certified := compare898 p (guard658 p guard)
  simpa only [at254, at279, Int.zero_add] using certified
theorem check658 (p : Pattern) : (!walkGuard soko1_2.board support p 254 279 .southWest || decide (bonus 254 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound658 p)
theorem guard659 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 281 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound659 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 281 .south = true) : bonus 255 p ≤ bonus 281 p := by
  have certified := compare898 p (guard659 p guard)
  simpa only [at255, at281, Int.zero_add] using certified
theorem check659 (p : Pattern) : (!walkGuard soko1_2.board support p 255 281 .south || decide (bonus 255 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound659 p)
theorem guard660 (p : Pattern) (guard : pushGuard support p 255 281 307 307 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound660 (p : Pattern) (guard : pushGuard support p 255 281 307 307 = true) : bonus 255 p ≤ 1 + Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some 307)) := by
  have certified := compare1005 p (guard660 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 281 (some 307))
  have normalized := agree0 _ _ (change_representative support p 281 (some 307) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check660 (p : Pattern) : (!pushGuard support p 255 281 307 307 || decide (bonus 255 p ≤ 1 + Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some 307)))) = true :=
  check_of_implication _ _ (bound660 p)
theorem guard661 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 256 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound661 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 256 .east = true) : bonus 255 p ≤ bonus 256 p := by
  have certified := compare898 p (guard661 p guard)
  simpa only [at255, at256, Int.zero_add] using certified
theorem check661 (p : Pattern) : (!walkGuard soko1_2.board support p 255 256 .east || decide (bonus 255 p ≤ bonus 256 p)) = true :=
  check_of_implication _ _ (bound661 p)
theorem guard662 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 254 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound662 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 254 .west = true) : bonus 255 p ≤ bonus 254 p := by
  have certified := compare898 p (guard662 p guard)
  simpa only [at255, at254, Int.zero_add] using certified
theorem check662 (p : Pattern) : (!walkGuard soko1_2.board support p 255 254 .west || decide (bonus 255 p ≤ bonus 254 p)) = true :=
  check_of_implication _ _ (bound662 p)
theorem guard663 (p : Pattern) (guard : pushGuard support p 255 254 253 253 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound663 (p : Pattern) (guard : pushGuard support p 255 254 253 253 = true) : bonus 255 p ≤ 1 + Generated.soko1_2Potential.boulder 253 - Generated.soko1_2Potential.boulder 254 + bonus 254 (change p 254 (some 253)) := by
  have certified := compare1005 p (guard663 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 254 (some 253))
  have normalized := agree0 _ _ (change_representative support p 254 (some 253) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check663 (p : Pattern) : (!pushGuard support p 255 254 253 253 || decide (bonus 255 p ≤ 1 + Generated.soko1_2Potential.boulder 253 - Generated.soko1_2Potential.boulder 254 + bonus 254 (change p 254 (some 253)))) = true :=
  check_of_implication _ _ (bound663 p)
theorem guard664 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 282 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound664 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 282 .southEast = true) : bonus 255 p ≤ bonus 282 p := by
  have certified := compare898 p (guard664 p guard)
  simpa only [at255, at282, Int.zero_add] using certified
theorem check664 (p : Pattern) : (!walkGuard soko1_2.board support p 255 282 .southEast || decide (bonus 255 p ≤ bonus 282 p)) = true :=
  check_of_implication _ _ (bound664 p)
theorem guard665 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 280 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound665 (p : Pattern) (guard : walkGuard soko1_2.board support p 255 280 .southWest = true) : bonus 255 p ≤ bonus 280 p := by
  have certified := compare898 p (guard665 p guard)
  simpa only [at255, at280, Int.zero_add] using certified
theorem check665 (p : Pattern) : (!walkGuard soko1_2.board support p 255 280 .southWest || decide (bonus 255 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound665 p)
theorem guard666 (p : Pattern) (guard : walkGuard soko1_2.board support p 256 282 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound666 (p : Pattern) (guard : walkGuard soko1_2.board support p 256 282 .south = true) : bonus 256 p ≤ bonus 282 p := by
  have certified := compare898 p (guard666 p guard)
  simpa only [at256, at282, Int.zero_add] using certified
theorem check666 (p : Pattern) : (!walkGuard soko1_2.board support p 256 282 .south || decide (bonus 256 p ≤ bonus 282 p)) = true :=
  check_of_implication _ _ (bound666 p)
theorem guard667 (p : Pattern) (guard : pushGuard support p 256 282 308 308 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound667 (p : Pattern) (guard : pushGuard support p 256 282 308 308 = true) : bonus 256 p ≤ 1 + Generated.soko1_2Potential.boulder 308 - Generated.soko1_2Potential.boulder 282 + bonus 282 (change p 282 (some 308)) := by
  have certified := compare1005 p (guard667 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 282 (some 308))
  have normalized := agree0 _ _ (change_representative support p 282 (some 308) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check667 (p : Pattern) : (!pushGuard support p 256 282 308 308 || decide (bonus 256 p ≤ 1 + Generated.soko1_2Potential.boulder 308 - Generated.soko1_2Potential.boulder 282 + bonus 282 (change p 282 (some 308)))) = true :=
  check_of_implication _ _ (bound667 p)
theorem guard668 (p : Pattern) (guard : walkGuard soko1_2.board support p 256 255 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound668 (p : Pattern) (guard : walkGuard soko1_2.board support p 256 255 .west = true) : bonus 256 p ≤ bonus 255 p := by
  have certified := compare898 p (guard668 p guard)
  simpa only [at256, at255, Int.zero_add] using certified
theorem check668 (p : Pattern) : (!walkGuard soko1_2.board support p 256 255 .west || decide (bonus 256 p ≤ bonus 255 p)) = true :=
  check_of_implication _ _ (bound668 p)
theorem guard669 (p : Pattern) (guard : pushGuard support p 256 255 254 254 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound669 (p : Pattern) (guard : pushGuard support p 256 255 254 254 = true) : bonus 256 p ≤ 1 + Generated.soko1_2Potential.boulder 254 - Generated.soko1_2Potential.boulder 255 + bonus 255 (change p 255 (some 254)) := by
  have certified := compare1005 p (guard669 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 255 (some 254))
  have normalized := agree0 _ _ (change_representative support p 255 (some 254) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check669 (p : Pattern) : (!pushGuard support p 256 255 254 254 || decide (bonus 256 p ≤ 1 + Generated.soko1_2Potential.boulder 254 - Generated.soko1_2Potential.boulder 255 + bonus 255 (change p 255 (some 254)))) = true :=
  check_of_implication _ _ (bound669 p)
theorem guard670 (p : Pattern) (guard : walkGuard soko1_2.board support p 256 281 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound670 (p : Pattern) (guard : walkGuard soko1_2.board support p 256 281 .southWest = true) : bonus 256 p ≤ bonus 281 p := by
  have certified := compare898 p (guard670 p guard)
  simpa only [at256, at281, Int.zero_add] using certified
theorem check670 (p : Pattern) : (!walkGuard soko1_2.board support p 256 281 .southWest || decide (bonus 256 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound670 p)
theorem guard671 (p : Pattern) (guard : walkGuard soko1_2.board support p 258 232 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound671 (p : Pattern) (guard : walkGuard soko1_2.board support p 258 232 .north = true) : bonus 258 p ≤ bonus 232 p := by
  have certified := compare0 p (guard671 p guard)
  simpa only [at258, at232, Int.zero_add] using certified
theorem check671 (p : Pattern) : (!walkGuard soko1_2.board support p 258 232 .north || decide (bonus 258 p ≤ bonus 232 p)) = true :=
  check_of_implication _ _ (bound671 p)
end NetHack.Sokoban12CostPartition
