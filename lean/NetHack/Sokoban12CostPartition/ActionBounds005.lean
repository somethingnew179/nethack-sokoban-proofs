import NetHack.Sokoban12CostPartition.ActionBounds004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard120 (p : Pattern) (guard : pushGuard support p 46 47 48 48 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound120 (p : Pattern) (guard : pushGuard support p 46 47 48 48 = true) : bonus 46 p ≤ 1 - Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.hole 48 + bonus 47 (change p 47 none) := by
  have certified := compare3 p (guard120 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 47 none)
  have normalized := agree75 _ _ (change_representative support p 47 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check120 (p : Pattern) : (!pushGuard support p 46 47 48 48 || decide (bonus 46 p ≤ 1 - Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.hole 48 + bonus 47 (change p 47 none))) = true :=
  check_of_implication _ _ (bound120 p)
theorem guard121 (p : Pattern) (guard : walkGuard soko1_2.board support p 46 45 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound121 (p : Pattern) (guard : walkGuard soko1_2.board support p 46 45 .west = true) : bonus 46 p ≤ bonus 45 p := by
  have certified := compare0 p (guard121 p guard)
  simpa only [at46, at45, Int.zero_add] using certified
theorem check121 (p : Pattern) : (!walkGuard soko1_2.board support p 46 45 .west || decide (bonus 46 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound121 p)
theorem guard122 (p : Pattern) (guard : pushGuard support p 46 45 44 44 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound122 (p : Pattern) (guard : pushGuard support p 46 45 44 44 = true) : bonus 46 p ≤ 1 + Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.boulder 45 + bonus 45 (change p 45 (some 44)) := by
  have certified := compare3 p (guard122 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 45 (some 44))
  have normalized := agree75 _ _ (change_representative support p 45 (some 44) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check122 (p : Pattern) : (!pushGuard support p 46 45 44 44 || decide (bonus 46 p ≤ 1 + Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.boulder 45 + bonus 45 (change p 45 (some 44)))) = true :=
  check_of_implication _ _ (bound122 p)
theorem guard123 (p : Pattern) (guard : pushGuard support p 46 45 44 44 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound123 (p : Pattern) (guard : pushGuard support p 46 45 44 44 = true) : bonus 46 p ≤ 1 - Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.hole 44 + bonus 45 (change p 45 none) := by
  have certified := compare3 p (guard123 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 45 none)
  have normalized := agree75 _ _ (change_representative support p 45 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check123 (p : Pattern) : (!pushGuard support p 46 45 44 44 || decide (bonus 46 p ≤ 1 - Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.hole 44 + bonus 45 (change p 45 none))) = true :=
  check_of_implication _ _ (bound123 p)
theorem guard124 (p : Pattern) (guard : walkGuard soko1_2.board support p 47 48 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound124 (p : Pattern) (guard : walkGuard soko1_2.board support p 47 48 .east = true) : bonus 47 p ≤ bonus 48 p := by
  have certified := compare0 p (guard124 p guard)
  simpa only [at47, at48, Int.zero_add] using certified
theorem check124 (p : Pattern) : (!walkGuard soko1_2.board support p 47 48 .east || decide (bonus 47 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound124 p)
theorem guard125 (p : Pattern) (guard : pushGuard support p 47 48 49 49 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound125 (p : Pattern) (guard : pushGuard support p 47 48 49 49 = true) : bonus 47 p ≤ 1 + Generated.soko1_2Potential.boulder 49 - Generated.soko1_2Potential.boulder 48 + bonus 48 (change p 48 (some 49)) := by
  have certified := compare3 p (guard125 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 48 (some 49))
  have normalized := agree75 _ _ (change_representative support p 48 (some 49) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check125 (p : Pattern) : (!pushGuard support p 47 48 49 49 || decide (bonus 47 p ≤ 1 + Generated.soko1_2Potential.boulder 49 - Generated.soko1_2Potential.boulder 48 + bonus 48 (change p 48 (some 49)))) = true :=
  check_of_implication _ _ (bound125 p)
theorem guard126 (p : Pattern) (guard : pushGuard support p 47 48 49 49 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound126 (p : Pattern) (guard : pushGuard support p 47 48 49 49 = true) : bonus 47 p ≤ 1 - Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.hole 49 + bonus 48 (change p 48 none) := by
  have certified := compare3 p (guard126 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 48 none)
  have normalized := agree75 _ _ (change_representative support p 48 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check126 (p : Pattern) : (!pushGuard support p 47 48 49 49 || decide (bonus 47 p ≤ 1 - Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.hole 49 + bonus 48 (change p 48 none))) = true :=
  check_of_implication _ _ (bound126 p)
theorem guard127 (p : Pattern) (guard : walkGuard soko1_2.board support p 47 46 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound127 (p : Pattern) (guard : walkGuard soko1_2.board support p 47 46 .west = true) : bonus 47 p ≤ bonus 46 p := by
  have certified := compare0 p (guard127 p guard)
  simpa only [at47, at46, Int.zero_add] using certified
theorem check127 (p : Pattern) : (!walkGuard soko1_2.board support p 47 46 .west || decide (bonus 47 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound127 p)
theorem guard128 (p : Pattern) (guard : pushGuard support p 47 46 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound128 (p : Pattern) (guard : pushGuard support p 47 46 45 45 = true) : bonus 47 p ≤ 1 + Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.boulder 46 + bonus 46 (change p 46 (some 45)) := by
  have certified := compare3 p (guard128 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 46 (some 45))
  have normalized := agree75 _ _ (change_representative support p 46 (some 45) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check128 (p : Pattern) : (!pushGuard support p 47 46 45 45 || decide (bonus 47 p ≤ 1 + Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.boulder 46 + bonus 46 (change p 46 (some 45)))) = true :=
  check_of_implication _ _ (bound128 p)
theorem guard129 (p : Pattern) (guard : pushGuard support p 47 46 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound129 (p : Pattern) (guard : pushGuard support p 47 46 45 45 = true) : bonus 47 p ≤ 1 - Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.hole 45 + bonus 46 (change p 46 none) := by
  have certified := compare3 p (guard129 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 46 none)
  have normalized := agree75 _ _ (change_representative support p 46 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check129 (p : Pattern) : (!pushGuard support p 47 46 45 45 || decide (bonus 47 p ≤ 1 - Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.hole 45 + bonus 46 (change p 46 none))) = true :=
  check_of_implication _ _ (bound129 p)
theorem guard130 (p : Pattern) (guard : walkGuard soko1_2.board support p 48 49 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound130 (p : Pattern) (guard : walkGuard soko1_2.board support p 48 49 .east = true) : bonus 48 p ≤ bonus 49 p := by
  have certified := compare0 p (guard130 p guard)
  simpa only [at48, at49, Int.zero_add] using certified
theorem check130 (p : Pattern) : (!walkGuard soko1_2.board support p 48 49 .east || decide (bonus 48 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound130 p)
theorem guard131 (p : Pattern) (guard : pushGuard support p 48 49 50 50 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound131 (p : Pattern) (guard : pushGuard support p 48 49 50 50 = true) : bonus 48 p ≤ 1 + Generated.soko1_2Potential.boulder 50 - Generated.soko1_2Potential.boulder 49 + bonus 49 (change p 49 (some 50)) := by
  have certified := compare4 p (guard131 p guard)
  change d75 p ≤ (19 : Int) + d75 (change p 49 (some 50))
  have normalized := agree75 _ _ (change_representative support p 49 (some 50) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (19 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check131 (p : Pattern) : (!pushGuard support p 48 49 50 50 || decide (bonus 48 p ≤ 1 + Generated.soko1_2Potential.boulder 50 - Generated.soko1_2Potential.boulder 49 + bonus 49 (change p 49 (some 50)))) = true :=
  check_of_implication _ _ (bound131 p)
theorem guard132 (p : Pattern) (guard : walkGuard soko1_2.board support p 48 47 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound132 (p : Pattern) (guard : walkGuard soko1_2.board support p 48 47 .west = true) : bonus 48 p ≤ bonus 47 p := by
  have certified := compare0 p (guard132 p guard)
  simpa only [at48, at47, Int.zero_add] using certified
theorem check132 (p : Pattern) : (!walkGuard soko1_2.board support p 48 47 .west || decide (bonus 48 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound132 p)
theorem guard133 (p : Pattern) (guard : pushGuard support p 48 47 46 46 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound133 (p : Pattern) (guard : pushGuard support p 48 47 46 46 = true) : bonus 48 p ≤ 1 + Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.boulder 47 + bonus 47 (change p 47 (some 46)) := by
  have certified := compare3 p (guard133 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 47 (some 46))
  have normalized := agree75 _ _ (change_representative support p 47 (some 46) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check133 (p : Pattern) : (!pushGuard support p 48 47 46 46 || decide (bonus 48 p ≤ 1 + Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.boulder 47 + bonus 47 (change p 47 (some 46)))) = true :=
  check_of_implication _ _ (bound133 p)
theorem guard134 (p : Pattern) (guard : pushGuard support p 48 47 46 46 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound134 (p : Pattern) (guard : pushGuard support p 48 47 46 46 = true) : bonus 48 p ≤ 1 - Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.hole 46 + bonus 47 (change p 47 none) := by
  have certified := compare3 p (guard134 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 47 none)
  have normalized := agree75 _ _ (change_representative support p 47 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check134 (p : Pattern) : (!pushGuard support p 48 47 46 46 || decide (bonus 48 p ≤ 1 - Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.hole 46 + bonus 47 (change p 47 none))) = true :=
  check_of_implication _ _ (bound134 p)
theorem guard135 (p : Pattern) (guard : walkGuard soko1_2.board support p 49 50 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound135 (p : Pattern) (guard : walkGuard soko1_2.board support p 49 50 .east = true) : bonus 49 p ≤ bonus 50 p := by
  have certified := compare0 p (guard135 p guard)
  simpa only [at49, at50, Int.zero_add] using certified
theorem check135 (p : Pattern) : (!walkGuard soko1_2.board support p 49 50 .east || decide (bonus 49 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound135 p)
theorem guard136 (p : Pattern) (guard : walkGuard soko1_2.board support p 49 48 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound136 (p : Pattern) (guard : walkGuard soko1_2.board support p 49 48 .west = true) : bonus 49 p ≤ bonus 48 p := by
  have certified := compare0 p (guard136 p guard)
  simpa only [at49, at48, Int.zero_add] using certified
theorem check136 (p : Pattern) : (!walkGuard soko1_2.board support p 49 48 .west || decide (bonus 49 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound136 p)
theorem guard137 (p : Pattern) (guard : pushGuard support p 49 48 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound137 (p : Pattern) (guard : pushGuard support p 49 48 47 47 = true) : bonus 49 p ≤ 1 + Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.boulder 48 + bonus 48 (change p 48 (some 47)) := by
  have certified := compare3 p (guard137 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 48 (some 47))
  have normalized := agree75 _ _ (change_representative support p 48 (some 47) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check137 (p : Pattern) : (!pushGuard support p 49 48 47 47 || decide (bonus 49 p ≤ 1 + Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.boulder 48 + bonus 48 (change p 48 (some 47)))) = true :=
  check_of_implication _ _ (bound137 p)
theorem guard138 (p : Pattern) (guard : pushGuard support p 49 48 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound138 (p : Pattern) (guard : pushGuard support p 49 48 47 47 = true) : bonus 49 p ≤ 1 - Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.hole 47 + bonus 48 (change p 48 none) := by
  have certified := compare3 p (guard138 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 48 none)
  have normalized := agree75 _ _ (change_representative support p 48 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check138 (p : Pattern) : (!pushGuard support p 49 48 47 47 || decide (bonus 49 p ≤ 1 - Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.hole 47 + bonus 48 (change p 48 none))) = true :=
  check_of_implication _ _ (bound138 p)
theorem guard139 (p : Pattern) (guard : walkGuard soko1_2.board support p 49 76 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound139 (p : Pattern) (guard : walkGuard soko1_2.board support p 49 76 .southEast = true) : bonus 49 p ≤ bonus 76 p := by
  have certified := compare0 p (guard139 p guard)
  simpa only [at49, at76, Int.zero_add] using certified
theorem check139 (p : Pattern) : (!walkGuard soko1_2.board support p 49 76 .southEast || decide (bonus 49 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound139 p)
theorem guard140 (p : Pattern) (guard : walkGuard soko1_2.board support p 50 76 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound140 (p : Pattern) (guard : walkGuard soko1_2.board support p 50 76 .south = true) : bonus 50 p ≤ bonus 76 p := by
  have certified := compare0 p (guard140 p guard)
  simpa only [at50, at76, Int.zero_add] using certified
theorem check140 (p : Pattern) : (!walkGuard soko1_2.board support p 50 76 .south || decide (bonus 50 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound140 p)
theorem guard141 (p : Pattern) (guard : pushGuard support p 50 76 102 102 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound141 (p : Pattern) (guard : pushGuard support p 50 76 102 102 = true) : bonus 50 p ≤ 1 + Generated.soko1_2Potential.boulder 102 - Generated.soko1_2Potential.boulder 76 + bonus 76 (change p 76 (some 102)) := by
  have certified := compare3 p (guard141 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 76 (some 102))
  have normalized := agree75 _ _ (change_representative support p 76 (some 102) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check141 (p : Pattern) : (!pushGuard support p 50 76 102 102 || decide (bonus 50 p ≤ 1 + Generated.soko1_2Potential.boulder 102 - Generated.soko1_2Potential.boulder 76 + bonus 76 (change p 76 (some 102)))) = true :=
  check_of_implication _ _ (bound141 p)
theorem guard142 (p : Pattern) (guard : walkGuard soko1_2.board support p 50 49 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound142 (p : Pattern) (guard : walkGuard soko1_2.board support p 50 49 .west = true) : bonus 50 p ≤ bonus 49 p := by
  have certified := compare0 p (guard142 p guard)
  simpa only [at50, at49, Int.zero_add] using certified
theorem check142 (p : Pattern) : (!walkGuard soko1_2.board support p 50 49 .west || decide (bonus 50 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound142 p)
theorem guard143 (p : Pattern) (guard : pushGuard support p 50 49 48 48 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound143 (p : Pattern) (guard : pushGuard support p 50 49 48 48 = true) : bonus 50 p ≤ 1 + Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.boulder 49 + bonus 49 (change p 49 (some 48)) := by
  have certified := compare3 p (guard143 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 49 (some 48))
  have normalized := agree75 _ _ (change_representative support p 49 (some 48) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check143 (p : Pattern) : (!pushGuard support p 50 49 48 48 || decide (bonus 50 p ≤ 1 + Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.boulder 49 + bonus 49 (change p 49 (some 48)))) = true :=
  check_of_implication _ _ (bound143 p)
end NetHack.Sokoban12CostPartition
