import NetHack.Sokoban12CostPartition.ActionBounds027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard672 (p : Pattern) (guard : pushGuard support p 258 232 206 206 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound672 (p : Pattern) (guard : pushGuard support p 258 232 206 206 = true) : bonus 258 p ≤ 1 + Generated.soko1_2Potential.boulder 206 - Generated.soko1_2Potential.boulder 232 + bonus 232 (change p 232 (some 206)) := by
  have certified := compare3 p (guard672 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 232 (some 206))
  have normalized := agree75 _ _ (change_representative support p 232 (some 206) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check672 (p : Pattern) : (!pushGuard support p 258 232 206 206 || decide (bonus 258 p ≤ 1 + Generated.soko1_2Potential.boulder 206 - Generated.soko1_2Potential.boulder 232 + bonus 232 (change p 232 (some 206)))) = true :=
  check_of_implication _ _ (bound672 p)
theorem guard673 (p : Pattern) (guard : walkGuard soko1_2.board support p 258 284 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound673 (p : Pattern) (guard : walkGuard soko1_2.board support p 258 284 .south = true) : bonus 258 p ≤ bonus 284 p := by
  have certified := compare0 p (guard673 p guard)
  simpa only [at258, at284, Int.zero_add] using certified
theorem check673 (p : Pattern) : (!walkGuard soko1_2.board support p 258 284 .south || decide (bonus 258 p ≤ bonus 284 p)) = true :=
  check_of_implication _ _ (bound673 p)
theorem guard674 (p : Pattern) (guard : pushGuard support p 258 284 310 310 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound674 (p : Pattern) (guard : pushGuard support p 258 284 310 310 = true) : bonus 258 p ≤ 1 + Generated.soko1_2Potential.boulder 310 - Generated.soko1_2Potential.boulder 284 + bonus 284 (change p 284 (some 310)) := by
  have certified := compare3 p (guard674 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 284 (some 310))
  have normalized := agree75 _ _ (change_representative support p 284 (some 310) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check674 (p : Pattern) : (!pushGuard support p 258 284 310 310 || decide (bonus 258 p ≤ 1 + Generated.soko1_2Potential.boulder 310 - Generated.soko1_2Potential.boulder 284 + bonus 284 (change p 284 (some 310)))) = true :=
  check_of_implication _ _ (bound674 p)
theorem guard675 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 236 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound675 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 236 .north = true) : bonus 262 p ≤ bonus 236 p := by
  have certified := compare897 p (guard675 p guard)
  simpa only [at262, at236, Int.zero_add] using certified
theorem check675 (p : Pattern) : (!walkGuard soko1_2.board support p 262 236 .north || decide (bonus 262 p ≤ bonus 236 p)) = true :=
  check_of_implication _ _ (bound675 p)
theorem guard676 (p : Pattern) (guard : pushGuard support p 262 236 210 210 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound676 (p : Pattern) (guard : pushGuard support p 262 236 210 210 = true) : bonus 262 p ≤ 1 + Generated.soko1_2Potential.boulder 210 - Generated.soko1_2Potential.boulder 236 + bonus 236 (change p 236 (some 210)) := by
  have certified := compare897 p (guard676 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 236 (some 210))
  have normalized := agree258 _ _ (change_representative support p 236 (some 210) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check676 (p : Pattern) : (!pushGuard support p 262 236 210 210 || decide (bonus 262 p ≤ 1 + Generated.soko1_2Potential.boulder 210 - Generated.soko1_2Potential.boulder 236 + bonus 236 (change p 236 (some 210)))) = true :=
  check_of_implication _ _ (bound676 p)
theorem guard677 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 288 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound677 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 288 .south = true) : bonus 262 p ≤ bonus 288 p := by
  have certified := compare897 p (guard677 p guard)
  simpa only [at262, at288, Int.zero_add] using certified
theorem check677 (p : Pattern) : (!walkGuard soko1_2.board support p 262 288 .south || decide (bonus 262 p ≤ bonus 288 p)) = true :=
  check_of_implication _ _ (bound677 p)
theorem guard678 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 263 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound678 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 263 .east = true) : bonus 262 p ≤ bonus 263 p := by
  have certified := compare897 p (guard678 p guard)
  simpa only [at262, at263, Int.zero_add] using certified
theorem check678 (p : Pattern) : (!walkGuard soko1_2.board support p 262 263 .east || decide (bonus 262 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound678 p)
theorem guard679 (p : Pattern) (guard : pushGuard support p 262 263 264 264 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound679 (p : Pattern) (guard : pushGuard support p 262 263 264 264 = true) : bonus 262 p ≤ 1 + Generated.soko1_2Potential.boulder 264 - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some 264)) := by
  have certified := compare897 p (guard679 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 263 (some 264))
  have normalized := agree258 _ _ (change_representative support p 263 (some 264) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check679 (p : Pattern) : (!pushGuard support p 262 263 264 264 || decide (bonus 262 p ≤ 1 + Generated.soko1_2Potential.boulder 264 - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some 264)))) = true :=
  check_of_implication _ _ (bound679 p)
theorem guard680 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 237 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound680 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 237 .northEast = true) : bonus 262 p ≤ bonus 237 p := by
  have certified := compare897 p (guard680 p guard)
  simpa only [at262, at237, Int.zero_add] using certified
theorem check680 (p : Pattern) : (!walkGuard soko1_2.board support p 262 237 .northEast || decide (bonus 262 p ≤ bonus 237 p)) = true :=
  check_of_implication _ _ (bound680 p)
theorem guard681 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 289 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound681 (p : Pattern) (guard : walkGuard soko1_2.board support p 262 289 .southEast = true) : bonus 262 p ≤ bonus 289 p := by
  have certified := compare897 p (guard681 p guard)
  simpa only [at262, at289, Int.zero_add] using certified
theorem check681 (p : Pattern) : (!walkGuard soko1_2.board support p 262 289 .southEast || decide (bonus 262 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound681 p)
theorem guard682 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 237 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound682 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 237 .north = true) : bonus 263 p ≤ bonus 237 p := by
  have certified := compare897 p (guard682 p guard)
  simpa only [at263, at237, Int.zero_add] using certified
theorem check682 (p : Pattern) : (!walkGuard soko1_2.board support p 263 237 .north || decide (bonus 263 p ≤ bonus 237 p)) = true :=
  check_of_implication _ _ (bound682 p)
theorem guard683 (p : Pattern) (guard : pushGuard support p 263 237 211 211 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound683 (p : Pattern) (guard : pushGuard support p 263 237 211 211 = true) : bonus 263 p ≤ 1 + Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some 211)) := by
  have certified := compare897 p (guard683 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 237 (some 211))
  have normalized := agree258 _ _ (change_representative support p 237 (some 211) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check683 (p : Pattern) : (!pushGuard support p 263 237 211 211 || decide (bonus 263 p ≤ 1 + Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some 211)))) = true :=
  check_of_implication _ _ (bound683 p)
theorem guard684 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 289 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound684 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 289 .south = true) : bonus 263 p ≤ bonus 289 p := by
  have certified := compare897 p (guard684 p guard)
  simpa only [at263, at289, Int.zero_add] using certified
theorem check684 (p : Pattern) : (!walkGuard soko1_2.board support p 263 289 .south || decide (bonus 263 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound684 p)
theorem guard685 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 264 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound685 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 264 .east = true) : bonus 263 p ≤ bonus 264 p := by
  have certified := compare897 p (guard685 p guard)
  simpa only [at263, at264, Int.zero_add] using certified
theorem check685 (p : Pattern) : (!walkGuard soko1_2.board support p 263 264 .east || decide (bonus 263 p ≤ bonus 264 p)) = true :=
  check_of_implication _ _ (bound685 p)
theorem guard686 (p : Pattern) (guard : pushGuard support p 263 264 265 265 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound686 (p : Pattern) (guard : pushGuard support p 263 264 265 265 = true) : bonus 263 p ≤ 1 + Generated.soko1_2Potential.boulder 265 - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some 265)) := by
  have certified := compare2570 p (guard686 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 264 (some 265))
  have normalized := agree258 _ _ (change_representative support p 264 (some 265) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check686 (p : Pattern) : (!pushGuard support p 263 264 265 265 || decide (bonus 263 p ≤ 1 + Generated.soko1_2Potential.boulder 265 - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some 265)))) = true :=
  check_of_implication _ _ (bound686 p)
theorem guard687 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 262 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound687 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 262 .west = true) : bonus 263 p ≤ bonus 262 p := by
  have certified := compare897 p (guard687 p guard)
  simpa only [at263, at262, Int.zero_add] using certified
theorem check687 (p : Pattern) : (!walkGuard soko1_2.board support p 263 262 .west || decide (bonus 263 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound687 p)
theorem guard688 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 238 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound688 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 238 .northEast = true) : bonus 263 p ≤ bonus 238 p := by
  have certified := compare897 p (guard688 p guard)
  simpa only [at263, at238, Int.zero_add] using certified
theorem check688 (p : Pattern) : (!walkGuard soko1_2.board support p 263 238 .northEast || decide (bonus 263 p ≤ bonus 238 p)) = true :=
  check_of_implication _ _ (bound688 p)
theorem guard689 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 236 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound689 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 236 .northWest = true) : bonus 263 p ≤ bonus 236 p := by
  have certified := compare897 p (guard689 p guard)
  simpa only [at263, at236, Int.zero_add] using certified
theorem check689 (p : Pattern) : (!walkGuard soko1_2.board support p 263 236 .northWest || decide (bonus 263 p ≤ bonus 236 p)) = true :=
  check_of_implication _ _ (bound689 p)
theorem guard690 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 290 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound690 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 290 .southEast = true) : bonus 263 p ≤ bonus 290 p := by
  have certified := compare897 p (guard690 p guard)
  simpa only [at263, at290, Int.zero_add] using certified
theorem check690 (p : Pattern) : (!walkGuard soko1_2.board support p 263 290 .southEast || decide (bonus 263 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound690 p)
theorem guard691 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 288 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound691 (p : Pattern) (guard : walkGuard soko1_2.board support p 263 288 .southWest = true) : bonus 263 p ≤ bonus 288 p := by
  have certified := compare897 p (guard691 p guard)
  simpa only [at263, at288, Int.zero_add] using certified
theorem check691 (p : Pattern) : (!walkGuard soko1_2.board support p 263 288 .southWest || decide (bonus 263 p ≤ bonus 288 p)) = true :=
  check_of_implication _ _ (bound691 p)
theorem guard692 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 238 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound692 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 238 .north = true) : bonus 264 p ≤ bonus 238 p := by
  have certified := compare897 p (guard692 p guard)
  simpa only [at264, at238, Int.zero_add] using certified
theorem check692 (p : Pattern) : (!walkGuard soko1_2.board support p 264 238 .north || decide (bonus 264 p ≤ bonus 238 p)) = true :=
  check_of_implication _ _ (bound692 p)
theorem guard693 (p : Pattern) (guard : pushGuard support p 264 238 212 212 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound693 (p : Pattern) (guard : pushGuard support p 264 238 212 212 = true) : bonus 264 p ≤ 1 + Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some 212)) := by
  have certified := compare897 p (guard693 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 238 (some 212))
  have normalized := agree258 _ _ (change_representative support p 238 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check693 (p : Pattern) : (!pushGuard support p 264 238 212 212 || decide (bonus 264 p ≤ 1 + Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some 212)))) = true :=
  check_of_implication _ _ (bound693 p)
theorem guard694 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 290 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound694 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 290 .south = true) : bonus 264 p ≤ bonus 290 p := by
  have certified := compare897 p (guard694 p guard)
  simpa only [at264, at290, Int.zero_add] using certified
theorem check694 (p : Pattern) : (!walkGuard soko1_2.board support p 264 290 .south || decide (bonus 264 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound694 p)
theorem guard695 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 265 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound695 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 265 .east = true) : bonus 264 p ≤ bonus 265 p := by
  have certified := compare897 p (guard695 p guard)
  simpa only [at264, at265, Int.zero_add] using certified
theorem check695 (p : Pattern) : (!walkGuard soko1_2.board support p 264 265 .east || decide (bonus 264 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound695 p)
end NetHack.Sokoban12CostPartition
