import NetHack.Sokoban32Refined.ActionBounds001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard48 (p : Pattern) (guard : pushGuard support p 47 48 49 49 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound48 (p : Pattern) (guard : pushGuard support p 47 48 49 49 = true) : bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder 49 - Generated.soko3_2Potential.boulder 48 + bonus 48 (change p 48 (some 49)) := by
  have certified := compare37 p (guard48 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 48 (some 49))
  have normalized := agree0 _ _ (change_representative support p 48 (some 49) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check48 (p : Pattern) : (!pushGuard support p 47 48 49 49 || decide (bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder 49 - Generated.soko3_2Potential.boulder 48 + bonus 48 (change p 48 (some 49)))) = true :=
  check_of_implication _ _ (bound48 p)
theorem guard49 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 46 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound49 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 46 .west = true) : bonus 47 p ≤ bonus 46 p := by
  have certified := compare103 p (guard49 p guard)
  simpa only [at47, at46, Int.zero_add] using certified
theorem check49 (p : Pattern) : (!walkGuard soko3_2.board support p 47 46 .west || decide (bonus 47 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound49 p)
theorem guard50 (p : Pattern) (guard : pushGuard support p 47 46 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound50 (p : Pattern) (guard : pushGuard support p 47 46 45 45 = true) : bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder 45 - Generated.soko3_2Potential.boulder 46 + bonus 46 (change p 46 (some 45)) := by
  have certified := compare37 p (guard50 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 46 (some 45))
  have normalized := agree0 _ _ (change_representative support p 46 (some 45) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check50 (p : Pattern) : (!pushGuard support p 47 46 45 45 || decide (bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder 45 - Generated.soko3_2Potential.boulder 46 + bonus 46 (change p 46 (some 45)))) = true :=
  check_of_implication _ _ (bound50 p)
theorem guard51 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 74 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound51 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 74 .southEast = true) : bonus 47 p ≤ bonus 74 p := by
  have certified := compare103 p (guard51 p guard)
  simpa only [at47, at74, Int.zero_add] using certified
theorem check51 (p : Pattern) : (!walkGuard soko3_2.board support p 47 74 .southEast || decide (bonus 47 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound51 p)
theorem guard52 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 72 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound52 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 72 .southWest = true) : bonus 47 p ≤ bonus 72 p := by
  have certified := compare103 p (guard52 p guard)
  simpa only [at47, at72, Int.zero_add] using certified
theorem check52 (p : Pattern) : (!walkGuard soko3_2.board support p 47 72 .southWest || decide (bonus 47 p ≤ bonus 72 p)) = true :=
  check_of_implication _ _ (bound52 p)
theorem guard53 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 74 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound53 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 74 .south = true) : bonus 48 p ≤ bonus 74 p := by
  have certified := compare103 p (guard53 p guard)
  simpa only [at48, at74, Int.zero_add] using certified
theorem check53 (p : Pattern) : (!walkGuard soko3_2.board support p 48 74 .south || decide (bonus 48 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound53 p)
theorem guard54 (p : Pattern) (guard : pushGuard support p 48 74 100 100 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound54 (p : Pattern) (guard : pushGuard support p 48 74 100 100 = true) : bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some 100)) := by
  have certified := compare37 p (guard54 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 74 (some 100))
  have normalized := agree0 _ _ (change_representative support p 74 (some 100) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check54 (p : Pattern) : (!pushGuard support p 48 74 100 100 || decide (bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some 100)))) = true :=
  check_of_implication _ _ (bound54 p)
theorem guard55 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 49 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound55 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 49 .east = true) : bonus 48 p ≤ bonus 49 p := by
  have certified := compare103 p (guard55 p guard)
  simpa only [at48, at49, Int.zero_add] using certified
theorem check55 (p : Pattern) : (!walkGuard soko3_2.board support p 48 49 .east || decide (bonus 48 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound55 p)
theorem guard56 (p : Pattern) (guard : pushGuard support p 48 49 50 50 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound56 (p : Pattern) (guard : pushGuard support p 48 49 50 50 = true) : bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder 50 - Generated.soko3_2Potential.boulder 49 + bonus 49 (change p 49 (some 50)) := by
  have certified := compare37 p (guard56 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 49 (some 50))
  have normalized := agree0 _ _ (change_representative support p 49 (some 50) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check56 (p : Pattern) : (!pushGuard support p 48 49 50 50 || decide (bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder 50 - Generated.soko3_2Potential.boulder 49 + bonus 49 (change p 49 (some 50)))) = true :=
  check_of_implication _ _ (bound56 p)
theorem guard57 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 47 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound57 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 47 .west = true) : bonus 48 p ≤ bonus 47 p := by
  have certified := compare103 p (guard57 p guard)
  simpa only [at48, at47, Int.zero_add] using certified
theorem check57 (p : Pattern) : (!walkGuard soko3_2.board support p 48 47 .west || decide (bonus 48 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound57 p)
theorem guard58 (p : Pattern) (guard : pushGuard support p 48 47 46 46 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound58 (p : Pattern) (guard : pushGuard support p 48 47 46 46 = true) : bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder 46 - Generated.soko3_2Potential.boulder 47 + bonus 47 (change p 47 (some 46)) := by
  have certified := compare37 p (guard58 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 47 (some 46))
  have normalized := agree0 _ _ (change_representative support p 47 (some 46) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check58 (p : Pattern) : (!pushGuard support p 48 47 46 46 || decide (bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder 46 - Generated.soko3_2Potential.boulder 47 + bonus 47 (change p 47 (some 46)))) = true :=
  check_of_implication _ _ (bound58 p)
theorem guard59 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 75 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound59 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 75 .southEast = true) : bonus 48 p ≤ bonus 75 p := by
  have certified := compare103 p (guard59 p guard)
  simpa only [at48, at75, Int.zero_add] using certified
theorem check59 (p : Pattern) : (!walkGuard soko3_2.board support p 48 75 .southEast || decide (bonus 48 p ≤ bonus 75 p)) = true :=
  check_of_implication _ _ (bound59 p)
theorem guard60 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 73 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound60 (p : Pattern) (guard : walkGuard soko3_2.board support p 48 73 .southWest = true) : bonus 48 p ≤ bonus 73 p := by
  have certified := compare103 p (guard60 p guard)
  simpa only [at48, at73, Int.zero_add] using certified
theorem check60 (p : Pattern) : (!walkGuard soko3_2.board support p 48 73 .southWest || decide (bonus 48 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound60 p)
theorem guard61 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 75 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound61 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 75 .south = true) : bonus 49 p ≤ bonus 75 p := by
  have certified := compare103 p (guard61 p guard)
  simpa only [at49, at75, Int.zero_add] using certified
theorem check61 (p : Pattern) : (!walkGuard soko3_2.board support p 49 75 .south || decide (bonus 49 p ≤ bonus 75 p)) = true :=
  check_of_implication _ _ (bound61 p)
theorem guard62 (p : Pattern) (guard : pushGuard support p 49 75 101 101 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound62 (p : Pattern) (guard : pushGuard support p 49 75 101 101 = true) : bonus 49 p ≤ 1 + Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some 101)) := by
  have certified := compare37 p (guard62 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 75 (some 101))
  have normalized := agree0 _ _ (change_representative support p 75 (some 101) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check62 (p : Pattern) : (!pushGuard support p 49 75 101 101 || decide (bonus 49 p ≤ 1 + Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some 101)))) = true :=
  check_of_implication _ _ (bound62 p)
theorem guard63 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 50 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound63 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 50 .east = true) : bonus 49 p ≤ bonus 50 p := by
  have certified := compare103 p (guard63 p guard)
  simpa only [at49, at50, Int.zero_add] using certified
theorem check63 (p : Pattern) : (!walkGuard soko3_2.board support p 49 50 .east || decide (bonus 49 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound63 p)
theorem guard64 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 48 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound64 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 48 .west = true) : bonus 49 p ≤ bonus 48 p := by
  have certified := compare103 p (guard64 p guard)
  simpa only [at49, at48, Int.zero_add] using certified
theorem check64 (p : Pattern) : (!walkGuard soko3_2.board support p 49 48 .west || decide (bonus 49 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound64 p)
theorem guard65 (p : Pattern) (guard : pushGuard support p 49 48 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound65 (p : Pattern) (guard : pushGuard support p 49 48 47 47 = true) : bonus 49 p ≤ 1 + Generated.soko3_2Potential.boulder 47 - Generated.soko3_2Potential.boulder 48 + bonus 48 (change p 48 (some 47)) := by
  have certified := compare37 p (guard65 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 48 (some 47))
  have normalized := agree0 _ _ (change_representative support p 48 (some 47) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check65 (p : Pattern) : (!pushGuard support p 49 48 47 47 || decide (bonus 49 p ≤ 1 + Generated.soko3_2Potential.boulder 47 - Generated.soko3_2Potential.boulder 48 + bonus 48 (change p 48 (some 47)))) = true :=
  check_of_implication _ _ (bound65 p)
theorem guard66 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 76 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound66 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 76 .southEast = true) : bonus 49 p ≤ bonus 76 p := by
  have certified := compare103 p (guard66 p guard)
  simpa only [at49, at76, Int.zero_add] using certified
theorem check66 (p : Pattern) : (!walkGuard soko3_2.board support p 49 76 .southEast || decide (bonus 49 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound66 p)
theorem guard67 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 74 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound67 (p : Pattern) (guard : walkGuard soko3_2.board support p 49 74 .southWest = true) : bonus 49 p ≤ bonus 74 p := by
  have certified := compare103 p (guard67 p guard)
  simpa only [at49, at74, Int.zero_add] using certified
theorem check67 (p : Pattern) : (!walkGuard soko3_2.board support p 49 74 .southWest || decide (bonus 49 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound67 p)
theorem guard68 (p : Pattern) (guard : walkGuard soko3_2.board support p 50 76 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound68 (p : Pattern) (guard : walkGuard soko3_2.board support p 50 76 .south = true) : bonus 50 p ≤ bonus 76 p := by
  have certified := compare103 p (guard68 p guard)
  simpa only [at50, at76, Int.zero_add] using certified
theorem check68 (p : Pattern) : (!walkGuard soko3_2.board support p 50 76 .south || decide (bonus 50 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound68 p)
theorem guard69 (p : Pattern) (guard : pushGuard support p 50 76 102 102 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound69 (p : Pattern) (guard : pushGuard support p 50 76 102 102 = true) : bonus 50 p ≤ 1 + Generated.soko3_2Potential.boulder 102 - Generated.soko3_2Potential.boulder 76 + bonus 76 (change p 76 (some 102)) := by
  have certified := compare37 p (guard69 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 76 (some 102))
  have normalized := agree0 _ _ (change_representative support p 76 (some 102) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check69 (p : Pattern) : (!pushGuard support p 50 76 102 102 || decide (bonus 50 p ≤ 1 + Generated.soko3_2Potential.boulder 102 - Generated.soko3_2Potential.boulder 76 + bonus 76 (change p 76 (some 102)))) = true :=
  check_of_implication _ _ (bound69 p)
theorem guard70 (p : Pattern) (guard : walkGuard soko3_2.board support p 50 49 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound70 (p : Pattern) (guard : walkGuard soko3_2.board support p 50 49 .west = true) : bonus 50 p ≤ bonus 49 p := by
  have certified := compare103 p (guard70 p guard)
  simpa only [at50, at49, Int.zero_add] using certified
theorem check70 (p : Pattern) : (!walkGuard soko3_2.board support p 50 49 .west || decide (bonus 50 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound70 p)
theorem guard71 (p : Pattern) (guard : pushGuard support p 50 49 48 48 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound71 (p : Pattern) (guard : pushGuard support p 50 49 48 48 = true) : bonus 50 p ≤ 1 + Generated.soko3_2Potential.boulder 48 - Generated.soko3_2Potential.boulder 49 + bonus 49 (change p 49 (some 48)) := by
  have certified := compare37 p (guard71 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 49 (some 48))
  have normalized := agree0 _ _ (change_representative support p 49 (some 48) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check71 (p : Pattern) : (!pushGuard support p 50 49 48 48 || decide (bonus 50 p ≤ 1 + Generated.soko3_2Potential.boulder 48 - Generated.soko3_2Potential.boulder 49 + bonus 49 (change p 49 (some 48)))) = true :=
  check_of_implication _ _ (bound71 p)
end NetHack.Sokoban32Refined
