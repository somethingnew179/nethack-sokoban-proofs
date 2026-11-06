import NetHack.Sokoban12CostPartition.ActionBounds001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard48 (p : Pattern) (guard : pushGuard support p 34 35 36 36 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound48 (p : Pattern) (guard : pushGuard support p 34 35 36 36 = true) : bonus 34 p ≤ 1 - Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.hole 36 + bonus 35 (change p 35 none) := by
  have certified := compare3 p (guard48 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 35 none)
  have normalized := agree75 _ _ (change_representative support p 35 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check48 (p : Pattern) : (!pushGuard support p 34 35 36 36 || decide (bonus 34 p ≤ 1 - Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.hole 36 + bonus 35 (change p 35 none))) = true :=
  check_of_implication _ _ (bound48 p)
theorem guard49 (p : Pattern) (guard : walkGuard soko1_2.board support p 34 33 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound49 (p : Pattern) (guard : walkGuard soko1_2.board support p 34 33 .west = true) : bonus 34 p ≤ bonus 33 p := by
  have certified := compare0 p (guard49 p guard)
  simpa only [at34, at33, Int.zero_add] using certified
theorem check49 (p : Pattern) : (!walkGuard soko1_2.board support p 34 33 .west || decide (bonus 34 p ≤ bonus 33 p)) = true :=
  check_of_implication _ _ (bound49 p)
theorem guard50 (p : Pattern) (guard : pushGuard support p 34 33 32 32 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound50 (p : Pattern) (guard : pushGuard support p 34 33 32 32 = true) : bonus 34 p ≤ 1 + Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.boulder 33 + bonus 33 (change p 33 (some 32)) := by
  have certified := compare3 p (guard50 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 33 (some 32))
  have normalized := agree75 _ _ (change_representative support p 33 (some 32) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check50 (p : Pattern) : (!pushGuard support p 34 33 32 32 || decide (bonus 34 p ≤ 1 + Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.boulder 33 + bonus 33 (change p 33 (some 32)))) = true :=
  check_of_implication _ _ (bound50 p)
theorem guard51 (p : Pattern) (guard : pushGuard support p 34 33 32 32 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound51 (p : Pattern) (guard : pushGuard support p 34 33 32 32 = true) : bonus 34 p ≤ 1 - Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.hole 32 + bonus 33 (change p 33 none) := by
  have certified := compare3 p (guard51 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 33 none)
  have normalized := agree75 _ _ (change_representative support p 33 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check51 (p : Pattern) : (!pushGuard support p 34 33 32 32 || decide (bonus 34 p ≤ 1 - Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.hole 32 + bonus 33 (change p 33 none))) = true :=
  check_of_implication _ _ (bound51 p)
theorem guard52 (p : Pattern) (guard : walkGuard soko1_2.board support p 35 36 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound52 (p : Pattern) (guard : walkGuard soko1_2.board support p 35 36 .east = true) : bonus 35 p ≤ bonus 36 p := by
  have certified := compare0 p (guard52 p guard)
  simpa only [at35, at36, Int.zero_add] using certified
theorem check52 (p : Pattern) : (!walkGuard soko1_2.board support p 35 36 .east || decide (bonus 35 p ≤ bonus 36 p)) = true :=
  check_of_implication _ _ (bound52 p)
theorem guard53 (p : Pattern) (guard : pushGuard support p 35 36 37 37 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound53 (p : Pattern) (guard : pushGuard support p 35 36 37 37 = true) : bonus 35 p ≤ 1 + Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.boulder 36 + bonus 36 (change p 36 (some 37)) := by
  have certified := compare3 p (guard53 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 36 (some 37))
  have normalized := agree75 _ _ (change_representative support p 36 (some 37) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check53 (p : Pattern) : (!pushGuard support p 35 36 37 37 || decide (bonus 35 p ≤ 1 + Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.boulder 36 + bonus 36 (change p 36 (some 37)))) = true :=
  check_of_implication _ _ (bound53 p)
theorem guard54 (p : Pattern) (guard : pushGuard support p 35 36 37 37 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound54 (p : Pattern) (guard : pushGuard support p 35 36 37 37 = true) : bonus 35 p ≤ 1 - Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.hole 37 + bonus 36 (change p 36 none) := by
  have certified := compare3 p (guard54 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 36 none)
  have normalized := agree75 _ _ (change_representative support p 36 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check54 (p : Pattern) : (!pushGuard support p 35 36 37 37 || decide (bonus 35 p ≤ 1 - Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.hole 37 + bonus 36 (change p 36 none))) = true :=
  check_of_implication _ _ (bound54 p)
theorem guard55 (p : Pattern) (guard : walkGuard soko1_2.board support p 35 34 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound55 (p : Pattern) (guard : walkGuard soko1_2.board support p 35 34 .west = true) : bonus 35 p ≤ bonus 34 p := by
  have certified := compare0 p (guard55 p guard)
  simpa only [at35, at34, Int.zero_add] using certified
theorem check55 (p : Pattern) : (!walkGuard soko1_2.board support p 35 34 .west || decide (bonus 35 p ≤ bonus 34 p)) = true :=
  check_of_implication _ _ (bound55 p)
theorem guard56 (p : Pattern) (guard : pushGuard support p 35 34 33 33 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound56 (p : Pattern) (guard : pushGuard support p 35 34 33 33 = true) : bonus 35 p ≤ 1 + Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.boulder 34 + bonus 34 (change p 34 (some 33)) := by
  have certified := compare3 p (guard56 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 34 (some 33))
  have normalized := agree75 _ _ (change_representative support p 34 (some 33) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check56 (p : Pattern) : (!pushGuard support p 35 34 33 33 || decide (bonus 35 p ≤ 1 + Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.boulder 34 + bonus 34 (change p 34 (some 33)))) = true :=
  check_of_implication _ _ (bound56 p)
theorem guard57 (p : Pattern) (guard : pushGuard support p 35 34 33 33 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound57 (p : Pattern) (guard : pushGuard support p 35 34 33 33 = true) : bonus 35 p ≤ 1 - Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.hole 33 + bonus 34 (change p 34 none) := by
  have certified := compare3 p (guard57 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 34 none)
  have normalized := agree75 _ _ (change_representative support p 34 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check57 (p : Pattern) : (!pushGuard support p 35 34 33 33 || decide (bonus 35 p ≤ 1 - Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.hole 33 + bonus 34 (change p 34 none))) = true :=
  check_of_implication _ _ (bound57 p)
theorem guard58 (p : Pattern) (guard : walkGuard soko1_2.board support p 36 37 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound58 (p : Pattern) (guard : walkGuard soko1_2.board support p 36 37 .east = true) : bonus 36 p ≤ bonus 37 p := by
  have certified := compare0 p (guard58 p guard)
  simpa only [at36, at37, Int.zero_add] using certified
theorem check58 (p : Pattern) : (!walkGuard soko1_2.board support p 36 37 .east || decide (bonus 36 p ≤ bonus 37 p)) = true :=
  check_of_implication _ _ (bound58 p)
theorem guard59 (p : Pattern) (guard : pushGuard support p 36 37 38 38 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound59 (p : Pattern) (guard : pushGuard support p 36 37 38 38 = true) : bonus 36 p ≤ 1 + Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.boulder 37 + bonus 37 (change p 37 (some 38)) := by
  have certified := compare3 p (guard59 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 37 (some 38))
  have normalized := agree75 _ _ (change_representative support p 37 (some 38) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check59 (p : Pattern) : (!pushGuard support p 36 37 38 38 || decide (bonus 36 p ≤ 1 + Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.boulder 37 + bonus 37 (change p 37 (some 38)))) = true :=
  check_of_implication _ _ (bound59 p)
theorem guard60 (p : Pattern) (guard : pushGuard support p 36 37 38 38 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound60 (p : Pattern) (guard : pushGuard support p 36 37 38 38 = true) : bonus 36 p ≤ 1 - Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.hole 38 + bonus 37 (change p 37 none) := by
  have certified := compare3 p (guard60 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 37 none)
  have normalized := agree75 _ _ (change_representative support p 37 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check60 (p : Pattern) : (!pushGuard support p 36 37 38 38 || decide (bonus 36 p ≤ 1 - Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.hole 38 + bonus 37 (change p 37 none))) = true :=
  check_of_implication _ _ (bound60 p)
theorem guard61 (p : Pattern) (guard : walkGuard soko1_2.board support p 36 35 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound61 (p : Pattern) (guard : walkGuard soko1_2.board support p 36 35 .west = true) : bonus 36 p ≤ bonus 35 p := by
  have certified := compare0 p (guard61 p guard)
  simpa only [at36, at35, Int.zero_add] using certified
theorem check61 (p : Pattern) : (!walkGuard soko1_2.board support p 36 35 .west || decide (bonus 36 p ≤ bonus 35 p)) = true :=
  check_of_implication _ _ (bound61 p)
theorem guard62 (p : Pattern) (guard : pushGuard support p 36 35 34 34 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound62 (p : Pattern) (guard : pushGuard support p 36 35 34 34 = true) : bonus 36 p ≤ 1 + Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.boulder 35 + bonus 35 (change p 35 (some 34)) := by
  have certified := compare3 p (guard62 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 35 (some 34))
  have normalized := agree75 _ _ (change_representative support p 35 (some 34) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check62 (p : Pattern) : (!pushGuard support p 36 35 34 34 || decide (bonus 36 p ≤ 1 + Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.boulder 35 + bonus 35 (change p 35 (some 34)))) = true :=
  check_of_implication _ _ (bound62 p)
theorem guard63 (p : Pattern) (guard : pushGuard support p 36 35 34 34 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound63 (p : Pattern) (guard : pushGuard support p 36 35 34 34 = true) : bonus 36 p ≤ 1 - Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.hole 34 + bonus 35 (change p 35 none) := by
  have certified := compare3 p (guard63 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 35 none)
  have normalized := agree75 _ _ (change_representative support p 35 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check63 (p : Pattern) : (!pushGuard support p 36 35 34 34 || decide (bonus 36 p ≤ 1 - Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.hole 34 + bonus 35 (change p 35 none))) = true :=
  check_of_implication _ _ (bound63 p)
theorem guard64 (p : Pattern) (guard : walkGuard soko1_2.board support p 37 38 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound64 (p : Pattern) (guard : walkGuard soko1_2.board support p 37 38 .east = true) : bonus 37 p ≤ bonus 38 p := by
  have certified := compare0 p (guard64 p guard)
  simpa only [at37, at38, Int.zero_add] using certified
theorem check64 (p : Pattern) : (!walkGuard soko1_2.board support p 37 38 .east || decide (bonus 37 p ≤ bonus 38 p)) = true :=
  check_of_implication _ _ (bound64 p)
theorem guard65 (p : Pattern) (guard : pushGuard support p 37 38 39 39 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound65 (p : Pattern) (guard : pushGuard support p 37 38 39 39 = true) : bonus 37 p ≤ 1 + Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.boulder 38 + bonus 38 (change p 38 (some 39)) := by
  have certified := compare3 p (guard65 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 38 (some 39))
  have normalized := agree75 _ _ (change_representative support p 38 (some 39) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check65 (p : Pattern) : (!pushGuard support p 37 38 39 39 || decide (bonus 37 p ≤ 1 + Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.boulder 38 + bonus 38 (change p 38 (some 39)))) = true :=
  check_of_implication _ _ (bound65 p)
theorem guard66 (p : Pattern) (guard : pushGuard support p 37 38 39 39 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound66 (p : Pattern) (guard : pushGuard support p 37 38 39 39 = true) : bonus 37 p ≤ 1 - Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.hole 39 + bonus 38 (change p 38 none) := by
  have certified := compare3 p (guard66 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 38 none)
  have normalized := agree75 _ _ (change_representative support p 38 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check66 (p : Pattern) : (!pushGuard support p 37 38 39 39 || decide (bonus 37 p ≤ 1 - Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.hole 39 + bonus 38 (change p 38 none))) = true :=
  check_of_implication _ _ (bound66 p)
theorem guard67 (p : Pattern) (guard : walkGuard soko1_2.board support p 37 36 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound67 (p : Pattern) (guard : walkGuard soko1_2.board support p 37 36 .west = true) : bonus 37 p ≤ bonus 36 p := by
  have certified := compare0 p (guard67 p guard)
  simpa only [at37, at36, Int.zero_add] using certified
theorem check67 (p : Pattern) : (!walkGuard soko1_2.board support p 37 36 .west || decide (bonus 37 p ≤ bonus 36 p)) = true :=
  check_of_implication _ _ (bound67 p)
theorem guard68 (p : Pattern) (guard : pushGuard support p 37 36 35 35 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound68 (p : Pattern) (guard : pushGuard support p 37 36 35 35 = true) : bonus 37 p ≤ 1 + Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.boulder 36 + bonus 36 (change p 36 (some 35)) := by
  have certified := compare3 p (guard68 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 36 (some 35))
  have normalized := agree75 _ _ (change_representative support p 36 (some 35) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check68 (p : Pattern) : (!pushGuard support p 37 36 35 35 || decide (bonus 37 p ≤ 1 + Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.boulder 36 + bonus 36 (change p 36 (some 35)))) = true :=
  check_of_implication _ _ (bound68 p)
theorem guard69 (p : Pattern) (guard : pushGuard support p 37 36 35 35 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound69 (p : Pattern) (guard : pushGuard support p 37 36 35 35 = true) : bonus 37 p ≤ 1 - Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.hole 35 + bonus 36 (change p 36 none) := by
  have certified := compare3 p (guard69 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 36 none)
  have normalized := agree75 _ _ (change_representative support p 36 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check69 (p : Pattern) : (!pushGuard support p 37 36 35 35 || decide (bonus 37 p ≤ 1 - Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.hole 35 + bonus 36 (change p 36 none))) = true :=
  check_of_implication _ _ (bound69 p)
theorem guard70 (p : Pattern) (guard : walkGuard soko1_2.board support p 38 39 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound70 (p : Pattern) (guard : walkGuard soko1_2.board support p 38 39 .east = true) : bonus 38 p ≤ bonus 39 p := by
  have certified := compare0 p (guard70 p guard)
  simpa only [at38, at39, Int.zero_add] using certified
theorem check70 (p : Pattern) : (!walkGuard soko1_2.board support p 38 39 .east || decide (bonus 38 p ≤ bonus 39 p)) = true :=
  check_of_implication _ _ (bound70 p)
theorem guard71 (p : Pattern) (guard : pushGuard support p 38 39 40 40 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound71 (p : Pattern) (guard : pushGuard support p 38 39 40 40 = true) : bonus 38 p ≤ 1 + Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.boulder 39 + bonus 39 (change p 39 (some 40)) := by
  have certified := compare3 p (guard71 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 39 (some 40))
  have normalized := agree75 _ _ (change_representative support p 39 (some 40) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check71 (p : Pattern) : (!pushGuard support p 38 39 40 40 || decide (bonus 38 p ≤ 1 + Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.boulder 39 + bonus 39 (change p 39 (some 40)))) = true :=
  check_of_implication _ _ (bound71 p)
end NetHack.Sokoban12CostPartition
