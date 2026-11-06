import NetHack.Sokoban32Refined.ActionBounds025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard624 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 177 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound624 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 177 .south = true) : bonus 151 p ≤ bonus 177 p := by
  have certified := compare103 p (guard624 p guard)
  simpa only [at151, at177, Int.zero_add] using certified
theorem check624 (p : Pattern) : (!walkGuard soko3_2.board support p 151 177 .south || decide (bonus 151 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound624 p)
theorem guard625 (p : Pattern) (guard : pushGuard support p 151 177 203 203 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound625 (p : Pattern) (guard : pushGuard support p 151 177 203 203 = true) : bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some 203)) := by
  have certified := compare37 p (guard625 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 177 (some 203))
  have normalized := agree0 _ _ (change_representative support p 177 (some 203) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check625 (p : Pattern) : (!pushGuard support p 151 177 203 203 || decide (bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some 203)))) = true :=
  check_of_implication _ _ (bound625 p)
theorem guard626 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 152 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound626 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 152 .east = true) : bonus 151 p ≤ bonus 152 p := by
  have certified := compare103 p (guard626 p guard)
  simpa only [at151, at152, Int.zero_add] using certified
theorem check626 (p : Pattern) : (!walkGuard soko3_2.board support p 151 152 .east || decide (bonus 151 p ≤ bonus 152 p)) = true :=
  check_of_implication _ _ (bound626 p)
theorem guard627 (p : Pattern) (guard : pushGuard support p 151 152 153 153 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound627 (p : Pattern) (guard : pushGuard support p 151 152 153 153 = true) : bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some 153)) := by
  have certified := compare37 p (guard627 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 152 (some 153))
  have normalized := agree0 _ _ (change_representative support p 152 (some 153) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check627 (p : Pattern) : (!pushGuard support p 151 152 153 153 || decide (bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some 153)))) = true :=
  check_of_implication _ _ (bound627 p)
theorem guard628 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 150 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound628 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 150 .west = true) : bonus 151 p ≤ bonus 150 p := by
  have certified := compare103 p (guard628 p guard)
  simpa only [at151, at150, Int.zero_add] using certified
theorem check628 (p : Pattern) : (!walkGuard soko3_2.board support p 151 150 .west || decide (bonus 151 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound628 p)
theorem guard629 (p : Pattern) (guard : pushGuard support p 151 150 149 149 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound629 (p : Pattern) (guard : pushGuard support p 151 150 149 149 = true) : bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some 149)) := by
  have certified := compare37 p (guard629 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 150 (some 149))
  have normalized := agree0 _ _ (change_representative support p 150 (some 149) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check629 (p : Pattern) : (!pushGuard support p 151 150 149 149 || decide (bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some 149)))) = true :=
  check_of_implication _ _ (bound629 p)
theorem guard630 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 126 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound630 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 126 .northEast = true) : bonus 151 p ≤ bonus 126 p := by
  have certified := compare103 p (guard630 p guard)
  simpa only [at151, at126, Int.zero_add] using certified
theorem check630 (p : Pattern) : (!walkGuard soko3_2.board support p 151 126 .northEast || decide (bonus 151 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound630 p)
theorem guard631 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 124 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound631 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 124 .northWest = true) : bonus 151 p ≤ bonus 124 p := by
  have certified := compare103 p (guard631 p guard)
  simpa only [at151, at124, Int.zero_add] using certified
theorem check631 (p : Pattern) : (!walkGuard soko3_2.board support p 151 124 .northWest || decide (bonus 151 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound631 p)
theorem guard632 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 178 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound632 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 178 .southEast = true) : bonus 151 p ≤ bonus 178 p := by
  have certified := compare103 p (guard632 p guard)
  simpa only [at151, at178, Int.zero_add] using certified
theorem check632 (p : Pattern) : (!walkGuard soko3_2.board support p 151 178 .southEast || decide (bonus 151 p ≤ bonus 178 p)) = true :=
  check_of_implication _ _ (bound632 p)
theorem guard633 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 176 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound633 (p : Pattern) (guard : walkGuard soko3_2.board support p 151 176 .southWest = true) : bonus 151 p ≤ bonus 176 p := by
  have certified := compare103 p (guard633 p guard)
  simpa only [at151, at176, Int.zero_add] using certified
theorem check633 (p : Pattern) : (!walkGuard soko3_2.board support p 151 176 .southWest || decide (bonus 151 p ≤ bonus 176 p)) = true :=
  check_of_implication _ _ (bound633 p)
theorem guard634 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 126 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound634 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 126 .north = true) : bonus 152 p ≤ bonus 126 p := by
  have certified := compare103 p (guard634 p guard)
  simpa only [at152, at126, Int.zero_add] using certified
theorem check634 (p : Pattern) : (!walkGuard soko3_2.board support p 152 126 .north || decide (bonus 152 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound634 p)
theorem guard635 (p : Pattern) (guard : pushGuard support p 152 126 100 100 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound635 (p : Pattern) (guard : pushGuard support p 152 126 100 100 = true) : bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some 100)) := by
  have certified := compare37 p (guard635 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 126 (some 100))
  have normalized := agree0 _ _ (change_representative support p 126 (some 100) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check635 (p : Pattern) : (!pushGuard support p 152 126 100 100 || decide (bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some 100)))) = true :=
  check_of_implication _ _ (bound635 p)
theorem guard636 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 178 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound636 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 178 .south = true) : bonus 152 p ≤ bonus 178 p := by
  have certified := compare103 p (guard636 p guard)
  simpa only [at152, at178, Int.zero_add] using certified
theorem check636 (p : Pattern) : (!walkGuard soko3_2.board support p 152 178 .south || decide (bonus 152 p ≤ bonus 178 p)) = true :=
  check_of_implication _ _ (bound636 p)
theorem guard637 (p : Pattern) (guard : pushGuard support p 152 178 204 204 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound637 (p : Pattern) (guard : pushGuard support p 152 178 204 204 = true) : bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some 204)) := by
  have certified := compare37 p (guard637 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 178 (some 204))
  have normalized := agree0 _ _ (change_representative support p 178 (some 204) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check637 (p : Pattern) : (!pushGuard support p 152 178 204 204 || decide (bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some 204)))) = true :=
  check_of_implication _ _ (bound637 p)
theorem guard638 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 153 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound638 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 153 .east = true) : bonus 152 p ≤ bonus 153 p := by
  have certified := compare103 p (guard638 p guard)
  simpa only [at152, at153, Int.zero_add] using certified
theorem check638 (p : Pattern) : (!walkGuard soko3_2.board support p 152 153 .east || decide (bonus 152 p ≤ bonus 153 p)) = true :=
  check_of_implication _ _ (bound638 p)
theorem guard639 (p : Pattern) (guard : pushGuard support p 152 153 154 154 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound639 (p : Pattern) (guard : pushGuard support p 152 153 154 154 = true) : bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder 154 - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some 154)) := by
  have certified := compare37 p (guard639 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 153 (some 154))
  have normalized := agree0 _ _ (change_representative support p 153 (some 154) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check639 (p : Pattern) : (!pushGuard support p 152 153 154 154 || decide (bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder 154 - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some 154)))) = true :=
  check_of_implication _ _ (bound639 p)
theorem guard640 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 151 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound640 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 151 .west = true) : bonus 152 p ≤ bonus 151 p := by
  have certified := compare103 p (guard640 p guard)
  simpa only [at152, at151, Int.zero_add] using certified
theorem check640 (p : Pattern) : (!walkGuard soko3_2.board support p 152 151 .west || decide (bonus 152 p ≤ bonus 151 p)) = true :=
  check_of_implication _ _ (bound640 p)
theorem guard641 (p : Pattern) (guard : pushGuard support p 152 151 150 150 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound641 (p : Pattern) (guard : pushGuard support p 152 151 150 150 = true) : bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some 150)) := by
  have certified := compare37 p (guard641 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 151 (some 150))
  have normalized := agree0 _ _ (change_representative support p 151 (some 150) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check641 (p : Pattern) : (!pushGuard support p 152 151 150 150 || decide (bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some 150)))) = true :=
  check_of_implication _ _ (bound641 p)
theorem guard642 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 127 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound642 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 127 .northEast = true) : bonus 152 p ≤ bonus 127 p := by
  have certified := compare103 p (guard642 p guard)
  simpa only [at152, at127, Int.zero_add] using certified
theorem check642 (p : Pattern) : (!walkGuard soko3_2.board support p 152 127 .northEast || decide (bonus 152 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound642 p)
theorem guard643 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 125 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound643 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 125 .northWest = true) : bonus 152 p ≤ bonus 125 p := by
  have certified := compare103 p (guard643 p guard)
  simpa only [at152, at125, Int.zero_add] using certified
theorem check643 (p : Pattern) : (!walkGuard soko3_2.board support p 152 125 .northWest || decide (bonus 152 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound643 p)
theorem guard644 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 179 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound644 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 179 .southEast = true) : bonus 152 p ≤ bonus 179 p := by
  have certified := compare103 p (guard644 p guard)
  simpa only [at152, at179, Int.zero_add] using certified
theorem check644 (p : Pattern) : (!walkGuard soko3_2.board support p 152 179 .southEast || decide (bonus 152 p ≤ bonus 179 p)) = true :=
  check_of_implication _ _ (bound644 p)
theorem guard645 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 177 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound645 (p : Pattern) (guard : walkGuard soko3_2.board support p 152 177 .southWest = true) : bonus 152 p ≤ bonus 177 p := by
  have certified := compare103 p (guard645 p guard)
  simpa only [at152, at177, Int.zero_add] using certified
theorem check645 (p : Pattern) : (!walkGuard soko3_2.board support p 152 177 .southWest || decide (bonus 152 p ≤ bonus 177 p)) = true :=
  check_of_implication _ _ (bound645 p)
theorem guard646 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 127 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound646 (p : Pattern) (guard : walkGuard soko3_2.board support p 153 127 .north = true) : bonus 153 p ≤ bonus 127 p := by
  have certified := compare103 p (guard646 p guard)
  simpa only [at153, at127, Int.zero_add] using certified
theorem check646 (p : Pattern) : (!walkGuard soko3_2.board support p 153 127 .north || decide (bonus 153 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound646 p)
theorem guard647 (p : Pattern) (guard : pushGuard support p 153 127 101 101 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound647 (p : Pattern) (guard : pushGuard support p 153 127 101 101 = true) : bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some 101)) := by
  have certified := compare37 p (guard647 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 127 (some 101))
  have normalized := agree0 _ _ (change_representative support p 127 (some 101) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check647 (p : Pattern) : (!pushGuard support p 153 127 101 101 || decide (bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some 101)))) = true :=
  check_of_implication _ _ (bound647 p)
end NetHack.Sokoban32Refined
