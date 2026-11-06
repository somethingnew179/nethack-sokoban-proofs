import NetHack.Sokoban12CostPartition.ActionBounds032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard792 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 264 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound792 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 264 .northEast = true) : bonus 289 p ≤ bonus 264 p := by
  have certified := compare897 p (guard792 p guard)
  simpa only [at289, at264, Int.zero_add] using certified
theorem check792 (p : Pattern) : (!walkGuard soko1_2.board support p 289 264 .northEast || decide (bonus 289 p ≤ bonus 264 p)) = true :=
  check_of_implication _ _ (bound792 p)
theorem guard793 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 262 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound793 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 262 .northWest = true) : bonus 289 p ≤ bonus 262 p := by
  have certified := compare897 p (guard793 p guard)
  simpa only [at289, at262, Int.zero_add] using certified
theorem check793 (p : Pattern) : (!walkGuard soko1_2.board support p 289 262 .northWest || decide (bonus 289 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound793 p)
theorem guard794 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 264 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound794 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 264 .north = true) : bonus 290 p ≤ bonus 264 p := by
  have certified := compare897 p (guard794 p guard)
  simpa only [at290, at264, Int.zero_add] using certified
theorem check794 (p : Pattern) : (!walkGuard soko1_2.board support p 290 264 .north || decide (bonus 290 p ≤ bonus 264 p)) = true :=
  check_of_implication _ _ (bound794 p)
theorem guard795 (p : Pattern) (guard : pushGuard support p 290 264 238 238 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound795 (p : Pattern) (guard : pushGuard support p 290 264 238 238 = true) : bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some 238)) := by
  have certified := compare897 p (guard795 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 264 (some 238))
  have normalized := agree258 _ _ (change_representative support p 264 (some 238) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check795 (p : Pattern) : (!pushGuard support p 290 264 238 238 || decide (bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some 238)))) = true :=
  check_of_implication _ _ (bound795 p)
theorem guard796 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 291 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound796 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 291 .east = true) : bonus 290 p ≤ bonus 291 p := by
  have certified := compare897 p (guard796 p guard)
  simpa only [at290, at291, Int.zero_add] using certified
theorem check796 (p : Pattern) : (!walkGuard soko1_2.board support p 290 291 .east || decide (bonus 290 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound796 p)
theorem guard797 (p : Pattern) (guard : pushGuard support p 290 291 292 292 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound797 (p : Pattern) (guard : pushGuard support p 290 291 292 292 = true) : bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder 292 - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some 292)) := by
  have certified := compare2570 p (guard797 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 291 (some 292))
  have normalized := agree258 _ _ (change_representative support p 291 (some 292) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check797 (p : Pattern) : (!pushGuard support p 290 291 292 292 || decide (bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder 292 - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some 292)))) = true :=
  check_of_implication _ _ (bound797 p)
theorem guard798 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 289 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound798 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 289 .west = true) : bonus 290 p ≤ bonus 289 p := by
  have certified := compare897 p (guard798 p guard)
  simpa only [at290, at289, Int.zero_add] using certified
theorem check798 (p : Pattern) : (!walkGuard soko1_2.board support p 290 289 .west || decide (bonus 290 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound798 p)
theorem guard799 (p : Pattern) (guard : pushGuard support p 290 289 288 288 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound799 (p : Pattern) (guard : pushGuard support p 290 289 288 288 = true) : bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder 288 - Generated.soko1_2Potential.boulder 289 + bonus 289 (change p 289 (some 288)) := by
  have certified := compare4441 p (guard799 p guard)
  change d258 p ≤ (5 : Int) + d258 (change p 289 (some 288))
  have normalized := agree258 _ _ (change_representative support p 289 (some 288) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (5 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check799 (p : Pattern) : (!pushGuard support p 290 289 288 288 || decide (bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder 288 - Generated.soko1_2Potential.boulder 289 + bonus 289 (change p 289 (some 288)))) = true :=
  check_of_implication _ _ (bound799 p)
theorem guard800 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 265 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound800 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 265 .northEast = true) : bonus 290 p ≤ bonus 265 p := by
  have certified := compare897 p (guard800 p guard)
  simpa only [at290, at265, Int.zero_add] using certified
theorem check800 (p : Pattern) : (!walkGuard soko1_2.board support p 290 265 .northEast || decide (bonus 290 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound800 p)
theorem guard801 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 263 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound801 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 263 .northWest = true) : bonus 290 p ≤ bonus 263 p := by
  have certified := compare897 p (guard801 p guard)
  simpa only [at290, at263, Int.zero_add] using certified
theorem check801 (p : Pattern) : (!walkGuard soko1_2.board support p 290 263 .northWest || decide (bonus 290 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound801 p)
theorem guard802 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 317 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound802 (p : Pattern) (guard : walkGuard soko1_2.board support p 290 317 .southEast = true) : bonus 290 p ≤ bonus 317 p := by
  have certified := compare897 p (guard802 p guard)
  simpa only [at290, at317, Int.zero_add] using certified
theorem check802 (p : Pattern) : (!walkGuard soko1_2.board support p 290 317 .southEast || decide (bonus 290 p ≤ bonus 317 p)) = true :=
  check_of_implication _ _ (bound802 p)
theorem guard803 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 265 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound803 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 265 .north = true) : bonus 291 p ≤ bonus 265 p := by
  have certified := compare897 p (guard803 p guard)
  simpa only [at291, at265, Int.zero_add] using certified
theorem check803 (p : Pattern) : (!walkGuard soko1_2.board support p 291 265 .north || decide (bonus 291 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound803 p)
theorem guard804 (p : Pattern) (guard : pushGuard support p 291 265 239 239 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound804 (p : Pattern) (guard : pushGuard support p 291 265 239 239 = true) : bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder 239 - Generated.soko1_2Potential.boulder 265 + bonus 265 (change p 265 (some 239)) := by
  have certified := compare897 p (guard804 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 265 (some 239))
  have normalized := agree258 _ _ (change_representative support p 265 (some 239) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check804 (p : Pattern) : (!pushGuard support p 291 265 239 239 || decide (bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder 239 - Generated.soko1_2Potential.boulder 265 + bonus 265 (change p 265 (some 239)))) = true :=
  check_of_implication _ _ (bound804 p)
theorem guard805 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 317 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound805 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 317 .south = true) : bonus 291 p ≤ bonus 317 p := by
  have certified := compare897 p (guard805 p guard)
  simpa only [at291, at317, Int.zero_add] using certified
theorem check805 (p : Pattern) : (!walkGuard soko1_2.board support p 291 317 .south || decide (bonus 291 p ≤ bonus 317 p)) = true :=
  check_of_implication _ _ (bound805 p)
theorem guard806 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 292 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound806 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 292 .east = true) : bonus 291 p ≤ bonus 292 p := by
  have certified := compare897 p (guard806 p guard)
  simpa only [at291, at292, Int.zero_add] using certified
theorem check806 (p : Pattern) : (!walkGuard soko1_2.board support p 291 292 .east || decide (bonus 291 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound806 p)
theorem guard807 (p : Pattern) (guard : pushGuard support p 291 292 293 293 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound807 (p : Pattern) (guard : pushGuard support p 291 292 293 293 = true) : bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder 293 - Generated.soko1_2Potential.boulder 292 + bonus 292 (change p 292 (some 293)) := by
  have certified := compare2570 p (guard807 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 292 (some 293))
  have normalized := agree258 _ _ (change_representative support p 292 (some 293) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check807 (p : Pattern) : (!pushGuard support p 291 292 293 293 || decide (bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder 293 - Generated.soko1_2Potential.boulder 292 + bonus 292 (change p 292 (some 293)))) = true :=
  check_of_implication _ _ (bound807 p)
theorem guard808 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 290 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound808 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 290 .west = true) : bonus 291 p ≤ bonus 290 p := by
  have certified := compare897 p (guard808 p guard)
  simpa only [at291, at290, Int.zero_add] using certified
theorem check808 (p : Pattern) : (!walkGuard soko1_2.board support p 291 290 .west || decide (bonus 291 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound808 p)
theorem guard809 (p : Pattern) (guard : pushGuard support p 291 290 289 289 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound809 (p : Pattern) (guard : pushGuard support p 291 290 289 289 = true) : bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder 289 - Generated.soko1_2Potential.boulder 290 + bonus 290 (change p 290 (some 289)) := by
  have certified := compare2570 p (guard809 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 290 (some 289))
  have normalized := agree258 _ _ (change_representative support p 290 (some 289) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check809 (p : Pattern) : (!pushGuard support p 291 290 289 289 || decide (bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder 289 - Generated.soko1_2Potential.boulder 290 + bonus 290 (change p 290 (some 289)))) = true :=
  check_of_implication _ _ (bound809 p)
theorem guard810 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 264 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound810 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 264 .northWest = true) : bonus 291 p ≤ bonus 264 p := by
  have certified := compare897 p (guard810 p guard)
  simpa only [at291, at264, Int.zero_add] using certified
theorem check810 (p : Pattern) : (!walkGuard soko1_2.board support p 291 264 .northWest || decide (bonus 291 p ≤ bonus 264 p)) = true :=
  check_of_implication _ _ (bound810 p)
theorem guard811 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 318 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound811 (p : Pattern) (guard : walkGuard soko1_2.board support p 291 318 .southEast = true) : bonus 291 p ≤ bonus 318 p := by
  have certified := compare897 p (guard811 p guard)
  simpa only [at291, at318, Int.zero_add] using certified
theorem check811 (p : Pattern) : (!walkGuard soko1_2.board support p 291 318 .southEast || decide (bonus 291 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound811 p)
theorem guard812 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 318 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound812 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 318 .south = true) : bonus 292 p ≤ bonus 318 p := by
  have certified := compare897 p (guard812 p guard)
  simpa only [at292, at318, Int.zero_add] using certified
theorem check812 (p : Pattern) : (!walkGuard soko1_2.board support p 292 318 .south || decide (bonus 292 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound812 p)
theorem guard813 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 293 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound813 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 293 .east = true) : bonus 292 p ≤ bonus 293 p := by
  have certified := compare897 p (guard813 p guard)
  simpa only [at292, at293, Int.zero_add] using certified
theorem check813 (p : Pattern) : (!walkGuard soko1_2.board support p 292 293 .east || decide (bonus 292 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound813 p)
theorem guard814 (p : Pattern) (guard : pushGuard support p 292 293 294 294 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound814 (p : Pattern) (guard : pushGuard support p 292 293 294 294 = true) : bonus 292 p ≤ 1 + Generated.soko1_2Potential.boulder 294 - Generated.soko1_2Potential.boulder 293 + bonus 293 (change p 293 (some 294)) := by
  have certified := compare4441 p (guard814 p guard)
  change d258 p ≤ (5 : Int) + d258 (change p 293 (some 294))
  have normalized := agree258 _ _ (change_representative support p 293 (some 294) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (5 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check814 (p : Pattern) : (!pushGuard support p 292 293 294 294 || decide (bonus 292 p ≤ 1 + Generated.soko1_2Potential.boulder 294 - Generated.soko1_2Potential.boulder 293 + bonus 293 (change p 293 (some 294)))) = true :=
  check_of_implication _ _ (bound814 p)
theorem guard815 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 291 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound815 (p : Pattern) (guard : walkGuard soko1_2.board support p 292 291 .west = true) : bonus 292 p ≤ bonus 291 p := by
  have certified := compare897 p (guard815 p guard)
  simpa only [at292, at291, Int.zero_add] using certified
theorem check815 (p : Pattern) : (!walkGuard soko1_2.board support p 292 291 .west || decide (bonus 292 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound815 p)
end NetHack.Sokoban12CostPartition
