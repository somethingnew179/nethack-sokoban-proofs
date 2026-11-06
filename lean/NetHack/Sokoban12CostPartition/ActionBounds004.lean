import NetHack.Sokoban12CostPartition.ActionBounds003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard96 (p : Pattern) (guard : pushGuard support p 42 43 44 44 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound96 (p : Pattern) (guard : pushGuard support p 42 43 44 44 = true) : bonus 42 p ≤ 1 - Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.hole 44 + bonus 43 (change p 43 none) := by
  have certified := compare3 p (guard96 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 43 none)
  have normalized := agree75 _ _ (change_representative support p 43 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check96 (p : Pattern) : (!pushGuard support p 42 43 44 44 || decide (bonus 42 p ≤ 1 - Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.hole 44 + bonus 43 (change p 43 none))) = true :=
  check_of_implication _ _ (bound96 p)
theorem guard97 (p : Pattern) (guard : walkGuard soko1_2.board support p 42 41 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound97 (p : Pattern) (guard : walkGuard soko1_2.board support p 42 41 .west = true) : bonus 42 p ≤ bonus 41 p := by
  have certified := compare0 p (guard97 p guard)
  simpa only [at42, at41, Int.zero_add] using certified
theorem check97 (p : Pattern) : (!walkGuard soko1_2.board support p 42 41 .west || decide (bonus 42 p ≤ bonus 41 p)) = true :=
  check_of_implication _ _ (bound97 p)
theorem guard98 (p : Pattern) (guard : pushGuard support p 42 41 40 40 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound98 (p : Pattern) (guard : pushGuard support p 42 41 40 40 = true) : bonus 42 p ≤ 1 + Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.boulder 41 + bonus 41 (change p 41 (some 40)) := by
  have certified := compare3 p (guard98 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 41 (some 40))
  have normalized := agree75 _ _ (change_representative support p 41 (some 40) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check98 (p : Pattern) : (!pushGuard support p 42 41 40 40 || decide (bonus 42 p ≤ 1 + Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.boulder 41 + bonus 41 (change p 41 (some 40)))) = true :=
  check_of_implication _ _ (bound98 p)
theorem guard99 (p : Pattern) (guard : pushGuard support p 42 41 40 40 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound99 (p : Pattern) (guard : pushGuard support p 42 41 40 40 = true) : bonus 42 p ≤ 1 - Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.hole 40 + bonus 41 (change p 41 none) := by
  have certified := compare3 p (guard99 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 41 none)
  have normalized := agree75 _ _ (change_representative support p 41 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check99 (p : Pattern) : (!pushGuard support p 42 41 40 40 || decide (bonus 42 p ≤ 1 - Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.hole 40 + bonus 41 (change p 41 none))) = true :=
  check_of_implication _ _ (bound99 p)
theorem guard100 (p : Pattern) (guard : walkGuard soko1_2.board support p 43 44 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound100 (p : Pattern) (guard : walkGuard soko1_2.board support p 43 44 .east = true) : bonus 43 p ≤ bonus 44 p := by
  have certified := compare0 p (guard100 p guard)
  simpa only [at43, at44, Int.zero_add] using certified
theorem check100 (p : Pattern) : (!walkGuard soko1_2.board support p 43 44 .east || decide (bonus 43 p ≤ bonus 44 p)) = true :=
  check_of_implication _ _ (bound100 p)
theorem guard101 (p : Pattern) (guard : pushGuard support p 43 44 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound101 (p : Pattern) (guard : pushGuard support p 43 44 45 45 = true) : bonus 43 p ≤ 1 + Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.boulder 44 + bonus 44 (change p 44 (some 45)) := by
  have certified := compare3 p (guard101 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 44 (some 45))
  have normalized := agree75 _ _ (change_representative support p 44 (some 45) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check101 (p : Pattern) : (!pushGuard support p 43 44 45 45 || decide (bonus 43 p ≤ 1 + Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.boulder 44 + bonus 44 (change p 44 (some 45)))) = true :=
  check_of_implication _ _ (bound101 p)
theorem guard102 (p : Pattern) (guard : pushGuard support p 43 44 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound102 (p : Pattern) (guard : pushGuard support p 43 44 45 45 = true) : bonus 43 p ≤ 1 - Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.hole 45 + bonus 44 (change p 44 none) := by
  have certified := compare3 p (guard102 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 44 none)
  have normalized := agree75 _ _ (change_representative support p 44 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check102 (p : Pattern) : (!pushGuard support p 43 44 45 45 || decide (bonus 43 p ≤ 1 - Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.hole 45 + bonus 44 (change p 44 none))) = true :=
  check_of_implication _ _ (bound102 p)
theorem guard103 (p : Pattern) (guard : walkGuard soko1_2.board support p 43 42 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound103 (p : Pattern) (guard : walkGuard soko1_2.board support p 43 42 .west = true) : bonus 43 p ≤ bonus 42 p := by
  have certified := compare0 p (guard103 p guard)
  simpa only [at43, at42, Int.zero_add] using certified
theorem check103 (p : Pattern) : (!walkGuard soko1_2.board support p 43 42 .west || decide (bonus 43 p ≤ bonus 42 p)) = true :=
  check_of_implication _ _ (bound103 p)
theorem guard104 (p : Pattern) (guard : pushGuard support p 43 42 41 41 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound104 (p : Pattern) (guard : pushGuard support p 43 42 41 41 = true) : bonus 43 p ≤ 1 + Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.boulder 42 + bonus 42 (change p 42 (some 41)) := by
  have certified := compare3 p (guard104 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 42 (some 41))
  have normalized := agree75 _ _ (change_representative support p 42 (some 41) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check104 (p : Pattern) : (!pushGuard support p 43 42 41 41 || decide (bonus 43 p ≤ 1 + Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.boulder 42 + bonus 42 (change p 42 (some 41)))) = true :=
  check_of_implication _ _ (bound104 p)
theorem guard105 (p : Pattern) (guard : pushGuard support p 43 42 41 41 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound105 (p : Pattern) (guard : pushGuard support p 43 42 41 41 = true) : bonus 43 p ≤ 1 - Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.hole 41 + bonus 42 (change p 42 none) := by
  have certified := compare3 p (guard105 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 42 none)
  have normalized := agree75 _ _ (change_representative support p 42 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check105 (p : Pattern) : (!pushGuard support p 43 42 41 41 || decide (bonus 43 p ≤ 1 - Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.hole 41 + bonus 42 (change p 42 none))) = true :=
  check_of_implication _ _ (bound105 p)
theorem guard106 (p : Pattern) (guard : walkGuard soko1_2.board support p 44 45 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound106 (p : Pattern) (guard : walkGuard soko1_2.board support p 44 45 .east = true) : bonus 44 p ≤ bonus 45 p := by
  have certified := compare0 p (guard106 p guard)
  simpa only [at44, at45, Int.zero_add] using certified
theorem check106 (p : Pattern) : (!walkGuard soko1_2.board support p 44 45 .east || decide (bonus 44 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound106 p)
theorem guard107 (p : Pattern) (guard : pushGuard support p 44 45 46 46 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound107 (p : Pattern) (guard : pushGuard support p 44 45 46 46 = true) : bonus 44 p ≤ 1 + Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.boulder 45 + bonus 45 (change p 45 (some 46)) := by
  have certified := compare3 p (guard107 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 45 (some 46))
  have normalized := agree75 _ _ (change_representative support p 45 (some 46) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check107 (p : Pattern) : (!pushGuard support p 44 45 46 46 || decide (bonus 44 p ≤ 1 + Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.boulder 45 + bonus 45 (change p 45 (some 46)))) = true :=
  check_of_implication _ _ (bound107 p)
theorem guard108 (p : Pattern) (guard : pushGuard support p 44 45 46 46 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound108 (p : Pattern) (guard : pushGuard support p 44 45 46 46 = true) : bonus 44 p ≤ 1 - Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.hole 46 + bonus 45 (change p 45 none) := by
  have certified := compare3 p (guard108 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 45 none)
  have normalized := agree75 _ _ (change_representative support p 45 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check108 (p : Pattern) : (!pushGuard support p 44 45 46 46 || decide (bonus 44 p ≤ 1 - Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.hole 46 + bonus 45 (change p 45 none))) = true :=
  check_of_implication _ _ (bound108 p)
theorem guard109 (p : Pattern) (guard : walkGuard soko1_2.board support p 44 43 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound109 (p : Pattern) (guard : walkGuard soko1_2.board support p 44 43 .west = true) : bonus 44 p ≤ bonus 43 p := by
  have certified := compare0 p (guard109 p guard)
  simpa only [at44, at43, Int.zero_add] using certified
theorem check109 (p : Pattern) : (!walkGuard soko1_2.board support p 44 43 .west || decide (bonus 44 p ≤ bonus 43 p)) = true :=
  check_of_implication _ _ (bound109 p)
theorem guard110 (p : Pattern) (guard : pushGuard support p 44 43 42 42 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound110 (p : Pattern) (guard : pushGuard support p 44 43 42 42 = true) : bonus 44 p ≤ 1 + Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.boulder 43 + bonus 43 (change p 43 (some 42)) := by
  have certified := compare3 p (guard110 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 43 (some 42))
  have normalized := agree75 _ _ (change_representative support p 43 (some 42) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check110 (p : Pattern) : (!pushGuard support p 44 43 42 42 || decide (bonus 44 p ≤ 1 + Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.boulder 43 + bonus 43 (change p 43 (some 42)))) = true :=
  check_of_implication _ _ (bound110 p)
theorem guard111 (p : Pattern) (guard : pushGuard support p 44 43 42 42 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound111 (p : Pattern) (guard : pushGuard support p 44 43 42 42 = true) : bonus 44 p ≤ 1 - Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.hole 42 + bonus 43 (change p 43 none) := by
  have certified := compare3 p (guard111 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 43 none)
  have normalized := agree75 _ _ (change_representative support p 43 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check111 (p : Pattern) : (!pushGuard support p 44 43 42 42 || decide (bonus 44 p ≤ 1 - Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.hole 42 + bonus 43 (change p 43 none))) = true :=
  check_of_implication _ _ (bound111 p)
theorem guard112 (p : Pattern) (guard : walkGuard soko1_2.board support p 45 46 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound112 (p : Pattern) (guard : walkGuard soko1_2.board support p 45 46 .east = true) : bonus 45 p ≤ bonus 46 p := by
  have certified := compare0 p (guard112 p guard)
  simpa only [at45, at46, Int.zero_add] using certified
theorem check112 (p : Pattern) : (!walkGuard soko1_2.board support p 45 46 .east || decide (bonus 45 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound112 p)
theorem guard113 (p : Pattern) (guard : pushGuard support p 45 46 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound113 (p : Pattern) (guard : pushGuard support p 45 46 47 47 = true) : bonus 45 p ≤ 1 + Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.boulder 46 + bonus 46 (change p 46 (some 47)) := by
  have certified := compare3 p (guard113 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 46 (some 47))
  have normalized := agree75 _ _ (change_representative support p 46 (some 47) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check113 (p : Pattern) : (!pushGuard support p 45 46 47 47 || decide (bonus 45 p ≤ 1 + Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.boulder 46 + bonus 46 (change p 46 (some 47)))) = true :=
  check_of_implication _ _ (bound113 p)
theorem guard114 (p : Pattern) (guard : pushGuard support p 45 46 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound114 (p : Pattern) (guard : pushGuard support p 45 46 47 47 = true) : bonus 45 p ≤ 1 - Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.hole 47 + bonus 46 (change p 46 none) := by
  have certified := compare3 p (guard114 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 46 none)
  have normalized := agree75 _ _ (change_representative support p 46 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check114 (p : Pattern) : (!pushGuard support p 45 46 47 47 || decide (bonus 45 p ≤ 1 - Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.hole 47 + bonus 46 (change p 46 none))) = true :=
  check_of_implication _ _ (bound114 p)
theorem guard115 (p : Pattern) (guard : walkGuard soko1_2.board support p 45 44 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound115 (p : Pattern) (guard : walkGuard soko1_2.board support p 45 44 .west = true) : bonus 45 p ≤ bonus 44 p := by
  have certified := compare0 p (guard115 p guard)
  simpa only [at45, at44, Int.zero_add] using certified
theorem check115 (p : Pattern) : (!walkGuard soko1_2.board support p 45 44 .west || decide (bonus 45 p ≤ bonus 44 p)) = true :=
  check_of_implication _ _ (bound115 p)
theorem guard116 (p : Pattern) (guard : pushGuard support p 45 44 43 43 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound116 (p : Pattern) (guard : pushGuard support p 45 44 43 43 = true) : bonus 45 p ≤ 1 + Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.boulder 44 + bonus 44 (change p 44 (some 43)) := by
  have certified := compare3 p (guard116 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 44 (some 43))
  have normalized := agree75 _ _ (change_representative support p 44 (some 43) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check116 (p : Pattern) : (!pushGuard support p 45 44 43 43 || decide (bonus 45 p ≤ 1 + Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.boulder 44 + bonus 44 (change p 44 (some 43)))) = true :=
  check_of_implication _ _ (bound116 p)
theorem guard117 (p : Pattern) (guard : pushGuard support p 45 44 43 43 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound117 (p : Pattern) (guard : pushGuard support p 45 44 43 43 = true) : bonus 45 p ≤ 1 - Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.hole 43 + bonus 44 (change p 44 none) := by
  have certified := compare3 p (guard117 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 44 none)
  have normalized := agree75 _ _ (change_representative support p 44 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check117 (p : Pattern) : (!pushGuard support p 45 44 43 43 || decide (bonus 45 p ≤ 1 - Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.hole 43 + bonus 44 (change p 44 none))) = true :=
  check_of_implication _ _ (bound117 p)
theorem guard118 (p : Pattern) (guard : walkGuard soko1_2.board support p 46 47 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound118 (p : Pattern) (guard : walkGuard soko1_2.board support p 46 47 .east = true) : bonus 46 p ≤ bonus 47 p := by
  have certified := compare0 p (guard118 p guard)
  simpa only [at46, at47, Int.zero_add] using certified
theorem check118 (p : Pattern) : (!walkGuard soko1_2.board support p 46 47 .east || decide (bonus 46 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound118 p)
theorem guard119 (p : Pattern) (guard : pushGuard support p 46 47 48 48 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound119 (p : Pattern) (guard : pushGuard support p 46 47 48 48 = true) : bonus 46 p ≤ 1 + Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.boulder 47 + bonus 47 (change p 47 (some 48)) := by
  have certified := compare3 p (guard119 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 47 (some 48))
  have normalized := agree75 _ _ (change_representative support p 47 (some 48) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check119 (p : Pattern) : (!pushGuard support p 46 47 48 48 || decide (bonus 46 p ≤ 1 + Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.boulder 47 + bonus 47 (change p 47 (some 48)))) = true :=
  check_of_implication _ _ (bound119 p)
end NetHack.Sokoban12CostPartition
