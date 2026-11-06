import NetHack.Sokoban12CostPartition.ActionBounds002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard72 (p : Pattern) (guard : pushGuard support p 38 39 40 40 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound72 (p : Pattern) (guard : pushGuard support p 38 39 40 40 = true) : bonus 38 p ≤ 1 - Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.hole 40 + bonus 39 (change p 39 none) := by
  have certified := compare3 p (guard72 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 39 none)
  have normalized := agree75 _ _ (change_representative support p 39 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check72 (p : Pattern) : (!pushGuard support p 38 39 40 40 || decide (bonus 38 p ≤ 1 - Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.hole 40 + bonus 39 (change p 39 none))) = true :=
  check_of_implication _ _ (bound72 p)
theorem guard73 (p : Pattern) (guard : walkGuard soko1_2.board support p 38 37 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound73 (p : Pattern) (guard : walkGuard soko1_2.board support p 38 37 .west = true) : bonus 38 p ≤ bonus 37 p := by
  have certified := compare0 p (guard73 p guard)
  simpa only [at38, at37, Int.zero_add] using certified
theorem check73 (p : Pattern) : (!walkGuard soko1_2.board support p 38 37 .west || decide (bonus 38 p ≤ bonus 37 p)) = true :=
  check_of_implication _ _ (bound73 p)
theorem guard74 (p : Pattern) (guard : pushGuard support p 38 37 36 36 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound74 (p : Pattern) (guard : pushGuard support p 38 37 36 36 = true) : bonus 38 p ≤ 1 + Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.boulder 37 + bonus 37 (change p 37 (some 36)) := by
  have certified := compare3 p (guard74 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 37 (some 36))
  have normalized := agree75 _ _ (change_representative support p 37 (some 36) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check74 (p : Pattern) : (!pushGuard support p 38 37 36 36 || decide (bonus 38 p ≤ 1 + Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.boulder 37 + bonus 37 (change p 37 (some 36)))) = true :=
  check_of_implication _ _ (bound74 p)
theorem guard75 (p : Pattern) (guard : pushGuard support p 38 37 36 36 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound75 (p : Pattern) (guard : pushGuard support p 38 37 36 36 = true) : bonus 38 p ≤ 1 - Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.hole 36 + bonus 37 (change p 37 none) := by
  have certified := compare3 p (guard75 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 37 none)
  have normalized := agree75 _ _ (change_representative support p 37 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check75 (p : Pattern) : (!pushGuard support p 38 37 36 36 || decide (bonus 38 p ≤ 1 - Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.hole 36 + bonus 37 (change p 37 none))) = true :=
  check_of_implication _ _ (bound75 p)
theorem guard76 (p : Pattern) (guard : walkGuard soko1_2.board support p 39 40 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound76 (p : Pattern) (guard : walkGuard soko1_2.board support p 39 40 .east = true) : bonus 39 p ≤ bonus 40 p := by
  have certified := compare0 p (guard76 p guard)
  simpa only [at39, at40, Int.zero_add] using certified
theorem check76 (p : Pattern) : (!walkGuard soko1_2.board support p 39 40 .east || decide (bonus 39 p ≤ bonus 40 p)) = true :=
  check_of_implication _ _ (bound76 p)
theorem guard77 (p : Pattern) (guard : pushGuard support p 39 40 41 41 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound77 (p : Pattern) (guard : pushGuard support p 39 40 41 41 = true) : bonus 39 p ≤ 1 + Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.boulder 40 + bonus 40 (change p 40 (some 41)) := by
  have certified := compare3 p (guard77 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 40 (some 41))
  have normalized := agree75 _ _ (change_representative support p 40 (some 41) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check77 (p : Pattern) : (!pushGuard support p 39 40 41 41 || decide (bonus 39 p ≤ 1 + Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.boulder 40 + bonus 40 (change p 40 (some 41)))) = true :=
  check_of_implication _ _ (bound77 p)
theorem guard78 (p : Pattern) (guard : pushGuard support p 39 40 41 41 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound78 (p : Pattern) (guard : pushGuard support p 39 40 41 41 = true) : bonus 39 p ≤ 1 - Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.hole 41 + bonus 40 (change p 40 none) := by
  have certified := compare3 p (guard78 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 40 none)
  have normalized := agree75 _ _ (change_representative support p 40 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check78 (p : Pattern) : (!pushGuard support p 39 40 41 41 || decide (bonus 39 p ≤ 1 - Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.hole 41 + bonus 40 (change p 40 none))) = true :=
  check_of_implication _ _ (bound78 p)
theorem guard79 (p : Pattern) (guard : walkGuard soko1_2.board support p 39 38 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound79 (p : Pattern) (guard : walkGuard soko1_2.board support p 39 38 .west = true) : bonus 39 p ≤ bonus 38 p := by
  have certified := compare0 p (guard79 p guard)
  simpa only [at39, at38, Int.zero_add] using certified
theorem check79 (p : Pattern) : (!walkGuard soko1_2.board support p 39 38 .west || decide (bonus 39 p ≤ bonus 38 p)) = true :=
  check_of_implication _ _ (bound79 p)
theorem guard80 (p : Pattern) (guard : pushGuard support p 39 38 37 37 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound80 (p : Pattern) (guard : pushGuard support p 39 38 37 37 = true) : bonus 39 p ≤ 1 + Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.boulder 38 + bonus 38 (change p 38 (some 37)) := by
  have certified := compare3 p (guard80 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 38 (some 37))
  have normalized := agree75 _ _ (change_representative support p 38 (some 37) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check80 (p : Pattern) : (!pushGuard support p 39 38 37 37 || decide (bonus 39 p ≤ 1 + Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.boulder 38 + bonus 38 (change p 38 (some 37)))) = true :=
  check_of_implication _ _ (bound80 p)
theorem guard81 (p : Pattern) (guard : pushGuard support p 39 38 37 37 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound81 (p : Pattern) (guard : pushGuard support p 39 38 37 37 = true) : bonus 39 p ≤ 1 - Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.hole 37 + bonus 38 (change p 38 none) := by
  have certified := compare3 p (guard81 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 38 none)
  have normalized := agree75 _ _ (change_representative support p 38 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check81 (p : Pattern) : (!pushGuard support p 39 38 37 37 || decide (bonus 39 p ≤ 1 - Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.hole 37 + bonus 38 (change p 38 none))) = true :=
  check_of_implication _ _ (bound81 p)
theorem guard82 (p : Pattern) (guard : walkGuard soko1_2.board support p 40 41 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound82 (p : Pattern) (guard : walkGuard soko1_2.board support p 40 41 .east = true) : bonus 40 p ≤ bonus 41 p := by
  have certified := compare0 p (guard82 p guard)
  simpa only [at40, at41, Int.zero_add] using certified
theorem check82 (p : Pattern) : (!walkGuard soko1_2.board support p 40 41 .east || decide (bonus 40 p ≤ bonus 41 p)) = true :=
  check_of_implication _ _ (bound82 p)
theorem guard83 (p : Pattern) (guard : pushGuard support p 40 41 42 42 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound83 (p : Pattern) (guard : pushGuard support p 40 41 42 42 = true) : bonus 40 p ≤ 1 + Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.boulder 41 + bonus 41 (change p 41 (some 42)) := by
  have certified := compare3 p (guard83 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 41 (some 42))
  have normalized := agree75 _ _ (change_representative support p 41 (some 42) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check83 (p : Pattern) : (!pushGuard support p 40 41 42 42 || decide (bonus 40 p ≤ 1 + Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.boulder 41 + bonus 41 (change p 41 (some 42)))) = true :=
  check_of_implication _ _ (bound83 p)
theorem guard84 (p : Pattern) (guard : pushGuard support p 40 41 42 42 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound84 (p : Pattern) (guard : pushGuard support p 40 41 42 42 = true) : bonus 40 p ≤ 1 - Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.hole 42 + bonus 41 (change p 41 none) := by
  have certified := compare3 p (guard84 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 41 none)
  have normalized := agree75 _ _ (change_representative support p 41 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check84 (p : Pattern) : (!pushGuard support p 40 41 42 42 || decide (bonus 40 p ≤ 1 - Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.hole 42 + bonus 41 (change p 41 none))) = true :=
  check_of_implication _ _ (bound84 p)
theorem guard85 (p : Pattern) (guard : walkGuard soko1_2.board support p 40 39 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound85 (p : Pattern) (guard : walkGuard soko1_2.board support p 40 39 .west = true) : bonus 40 p ≤ bonus 39 p := by
  have certified := compare0 p (guard85 p guard)
  simpa only [at40, at39, Int.zero_add] using certified
theorem check85 (p : Pattern) : (!walkGuard soko1_2.board support p 40 39 .west || decide (bonus 40 p ≤ bonus 39 p)) = true :=
  check_of_implication _ _ (bound85 p)
theorem guard86 (p : Pattern) (guard : pushGuard support p 40 39 38 38 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound86 (p : Pattern) (guard : pushGuard support p 40 39 38 38 = true) : bonus 40 p ≤ 1 + Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.boulder 39 + bonus 39 (change p 39 (some 38)) := by
  have certified := compare3 p (guard86 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 39 (some 38))
  have normalized := agree75 _ _ (change_representative support p 39 (some 38) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check86 (p : Pattern) : (!pushGuard support p 40 39 38 38 || decide (bonus 40 p ≤ 1 + Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.boulder 39 + bonus 39 (change p 39 (some 38)))) = true :=
  check_of_implication _ _ (bound86 p)
theorem guard87 (p : Pattern) (guard : pushGuard support p 40 39 38 38 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound87 (p : Pattern) (guard : pushGuard support p 40 39 38 38 = true) : bonus 40 p ≤ 1 - Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.hole 38 + bonus 39 (change p 39 none) := by
  have certified := compare3 p (guard87 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 39 none)
  have normalized := agree75 _ _ (change_representative support p 39 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check87 (p : Pattern) : (!pushGuard support p 40 39 38 38 || decide (bonus 40 p ≤ 1 - Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.hole 38 + bonus 39 (change p 39 none))) = true :=
  check_of_implication _ _ (bound87 p)
theorem guard88 (p : Pattern) (guard : walkGuard soko1_2.board support p 41 42 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound88 (p : Pattern) (guard : walkGuard soko1_2.board support p 41 42 .east = true) : bonus 41 p ≤ bonus 42 p := by
  have certified := compare0 p (guard88 p guard)
  simpa only [at41, at42, Int.zero_add] using certified
theorem check88 (p : Pattern) : (!walkGuard soko1_2.board support p 41 42 .east || decide (bonus 41 p ≤ bonus 42 p)) = true :=
  check_of_implication _ _ (bound88 p)
theorem guard89 (p : Pattern) (guard : pushGuard support p 41 42 43 43 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound89 (p : Pattern) (guard : pushGuard support p 41 42 43 43 = true) : bonus 41 p ≤ 1 + Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.boulder 42 + bonus 42 (change p 42 (some 43)) := by
  have certified := compare3 p (guard89 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 42 (some 43))
  have normalized := agree75 _ _ (change_representative support p 42 (some 43) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check89 (p : Pattern) : (!pushGuard support p 41 42 43 43 || decide (bonus 41 p ≤ 1 + Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.boulder 42 + bonus 42 (change p 42 (some 43)))) = true :=
  check_of_implication _ _ (bound89 p)
theorem guard90 (p : Pattern) (guard : pushGuard support p 41 42 43 43 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound90 (p : Pattern) (guard : pushGuard support p 41 42 43 43 = true) : bonus 41 p ≤ 1 - Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.hole 43 + bonus 42 (change p 42 none) := by
  have certified := compare3 p (guard90 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 42 none)
  have normalized := agree75 _ _ (change_representative support p 42 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check90 (p : Pattern) : (!pushGuard support p 41 42 43 43 || decide (bonus 41 p ≤ 1 - Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.hole 43 + bonus 42 (change p 42 none))) = true :=
  check_of_implication _ _ (bound90 p)
theorem guard91 (p : Pattern) (guard : walkGuard soko1_2.board support p 41 40 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound91 (p : Pattern) (guard : walkGuard soko1_2.board support p 41 40 .west = true) : bonus 41 p ≤ bonus 40 p := by
  have certified := compare0 p (guard91 p guard)
  simpa only [at41, at40, Int.zero_add] using certified
theorem check91 (p : Pattern) : (!walkGuard soko1_2.board support p 41 40 .west || decide (bonus 41 p ≤ bonus 40 p)) = true :=
  check_of_implication _ _ (bound91 p)
theorem guard92 (p : Pattern) (guard : pushGuard support p 41 40 39 39 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound92 (p : Pattern) (guard : pushGuard support p 41 40 39 39 = true) : bonus 41 p ≤ 1 + Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.boulder 40 + bonus 40 (change p 40 (some 39)) := by
  have certified := compare3 p (guard92 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 40 (some 39))
  have normalized := agree75 _ _ (change_representative support p 40 (some 39) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check92 (p : Pattern) : (!pushGuard support p 41 40 39 39 || decide (bonus 41 p ≤ 1 + Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.boulder 40 + bonus 40 (change p 40 (some 39)))) = true :=
  check_of_implication _ _ (bound92 p)
theorem guard93 (p : Pattern) (guard : pushGuard support p 41 40 39 39 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound93 (p : Pattern) (guard : pushGuard support p 41 40 39 39 = true) : bonus 41 p ≤ 1 - Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.hole 39 + bonus 40 (change p 40 none) := by
  have certified := compare3 p (guard93 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 40 none)
  have normalized := agree75 _ _ (change_representative support p 40 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check93 (p : Pattern) : (!pushGuard support p 41 40 39 39 || decide (bonus 41 p ≤ 1 - Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.hole 39 + bonus 40 (change p 40 none))) = true :=
  check_of_implication _ _ (bound93 p)
theorem guard94 (p : Pattern) (guard : walkGuard soko1_2.board support p 42 43 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound94 (p : Pattern) (guard : walkGuard soko1_2.board support p 42 43 .east = true) : bonus 42 p ≤ bonus 43 p := by
  have certified := compare0 p (guard94 p guard)
  simpa only [at42, at43, Int.zero_add] using certified
theorem check94 (p : Pattern) : (!walkGuard soko1_2.board support p 42 43 .east || decide (bonus 42 p ≤ bonus 43 p)) = true :=
  check_of_implication _ _ (bound94 p)
theorem guard95 (p : Pattern) (guard : pushGuard support p 42 43 44 44 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound95 (p : Pattern) (guard : pushGuard support p 42 43 44 44 = true) : bonus 42 p ≤ 1 + Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.boulder 43 + bonus 43 (change p 43 (some 44)) := by
  have certified := compare3 p (guard95 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 43 (some 44))
  have normalized := agree75 _ _ (change_representative support p 43 (some 44) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check95 (p : Pattern) : (!pushGuard support p 42 43 44 44 || decide (bonus 42 p ≤ 1 + Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.boulder 43 + bonus 43 (change p 43 (some 44)))) = true :=
  check_of_implication _ _ (bound95 p)
end NetHack.Sokoban12CostPartition
