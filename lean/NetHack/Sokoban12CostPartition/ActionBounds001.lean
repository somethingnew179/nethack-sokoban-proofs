import NetHack.Sokoban12CostPartition.ActionBounds000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard24 (p : Pattern) (guard : walkGuard soko1_2.board support p 30 31 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound24 (p : Pattern) (guard : walkGuard soko1_2.board support p 30 31 .east = true) : bonus 30 p ≤ bonus 31 p := by
  have certified := compare0 p (guard24 p guard)
  simpa only [at30, at31, Int.zero_add] using certified
theorem check24 (p : Pattern) : (!walkGuard soko1_2.board support p 30 31 .east || decide (bonus 30 p ≤ bonus 31 p)) = true :=
  check_of_implication _ _ (bound24 p)
theorem guard25 (p : Pattern) (guard : pushGuard support p 30 31 32 32 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound25 (p : Pattern) (guard : pushGuard support p 30 31 32 32 = true) : bonus 30 p ≤ 1 + Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.boulder 31 + bonus 31 (change p 31 (some 32)) := by
  have certified := compare0 p (guard25 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 31 (some 32))
  have normalized := agree75 _ _ (change_representative support p 31 (some 32) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check25 (p : Pattern) : (!pushGuard support p 30 31 32 32 || decide (bonus 30 p ≤ 1 + Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.boulder 31 + bonus 31 (change p 31 (some 32)))) = true :=
  check_of_implication _ _ (bound25 p)
theorem guard26 (p : Pattern) (guard : pushGuard support p 30 31 32 32 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound26 (p : Pattern) (guard : pushGuard support p 30 31 32 32 = true) : bonus 30 p ≤ 1 - Generated.soko1_2Potential.boulder 31 - Generated.soko1_2Potential.hole 32 + bonus 31 (change p 31 none) := by
  have certified := compare0 p (guard26 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 31 none)
  have normalized := agree75 _ _ (change_representative support p 31 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check26 (p : Pattern) : (!pushGuard support p 30 31 32 32 || decide (bonus 30 p ≤ 1 - Generated.soko1_2Potential.boulder 31 - Generated.soko1_2Potential.hole 32 + bonus 31 (change p 31 none))) = true :=
  check_of_implication _ _ (bound26 p)
theorem guard27 (p : Pattern) (guard : walkGuard soko1_2.board support p 30 29 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound27 (p : Pattern) (guard : walkGuard soko1_2.board support p 30 29 .west = true) : bonus 30 p ≤ bonus 29 p := by
  have certified := compare0 p (guard27 p guard)
  simpa only [at30, at29, Int.zero_add] using certified
theorem check27 (p : Pattern) : (!walkGuard soko1_2.board support p 30 29 .west || decide (bonus 30 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound27 p)
theorem guard28 (p : Pattern) (guard : walkGuard soko1_2.board support p 30 55 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound28 (p : Pattern) (guard : walkGuard soko1_2.board support p 30 55 .southWest = true) : bonus 30 p ≤ bonus 55 p := by
  have certified := compare0 p (guard28 p guard)
  simpa only [at30, at55, Int.zero_add] using certified
theorem check28 (p : Pattern) : (!walkGuard soko1_2.board support p 30 55 .southWest || decide (bonus 30 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound28 p)
theorem guard29 (p : Pattern) (guard : walkGuard soko1_2.board support p 31 32 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound29 (p : Pattern) (guard : walkGuard soko1_2.board support p 31 32 .east = true) : bonus 31 p ≤ bonus 32 p := by
  have certified := compare0 p (guard29 p guard)
  simpa only [at31, at32, Int.zero_add] using certified
theorem check29 (p : Pattern) : (!walkGuard soko1_2.board support p 31 32 .east || decide (bonus 31 p ≤ bonus 32 p)) = true :=
  check_of_implication _ _ (bound29 p)
theorem guard30 (p : Pattern) (guard : pushGuard support p 31 32 33 33 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound30 (p : Pattern) (guard : pushGuard support p 31 32 33 33 = true) : bonus 31 p ≤ 1 + Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.boulder 32 + bonus 32 (change p 32 (some 33)) := by
  have certified := compare3 p (guard30 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 32 (some 33))
  have normalized := agree75 _ _ (change_representative support p 32 (some 33) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check30 (p : Pattern) : (!pushGuard support p 31 32 33 33 || decide (bonus 31 p ≤ 1 + Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.boulder 32 + bonus 32 (change p 32 (some 33)))) = true :=
  check_of_implication _ _ (bound30 p)
theorem guard31 (p : Pattern) (guard : pushGuard support p 31 32 33 33 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound31 (p : Pattern) (guard : pushGuard support p 31 32 33 33 = true) : bonus 31 p ≤ 1 - Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.hole 33 + bonus 32 (change p 32 none) := by
  have certified := compare3 p (guard31 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 32 none)
  have normalized := agree75 _ _ (change_representative support p 32 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check31 (p : Pattern) : (!pushGuard support p 31 32 33 33 || decide (bonus 31 p ≤ 1 - Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.hole 33 + bonus 32 (change p 32 none))) = true :=
  check_of_implication _ _ (bound31 p)
theorem guard32 (p : Pattern) (guard : walkGuard soko1_2.board support p 31 30 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound32 (p : Pattern) (guard : walkGuard soko1_2.board support p 31 30 .west = true) : bonus 31 p ≤ bonus 30 p := by
  have certified := compare0 p (guard32 p guard)
  simpa only [at31, at30, Int.zero_add] using certified
theorem check32 (p : Pattern) : (!walkGuard soko1_2.board support p 31 30 .west || decide (bonus 31 p ≤ bonus 30 p)) = true :=
  check_of_implication _ _ (bound32 p)
theorem guard33 (p : Pattern) (guard : pushGuard support p 31 30 29 29 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound33 (p : Pattern) (guard : pushGuard support p 31 30 29 29 = true) : bonus 31 p ≤ 1 + Generated.soko1_2Potential.boulder 29 - Generated.soko1_2Potential.boulder 30 + bonus 30 (change p 30 (some 29)) := by
  have certified := compare1 p (guard33 p guard)
  change d75 p ≤ (18 : Int) + d75 (change p 30 (some 29))
  have normalized := agree75 _ _ (change_representative support p 30 (some 29) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (18 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check33 (p : Pattern) : (!pushGuard support p 31 30 29 29 || decide (bonus 31 p ≤ 1 + Generated.soko1_2Potential.boulder 29 - Generated.soko1_2Potential.boulder 30 + bonus 30 (change p 30 (some 29)))) = true :=
  check_of_implication _ _ (bound33 p)
theorem guard34 (p : Pattern) (guard : walkGuard soko1_2.board support p 31 56 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound34 (p : Pattern) (guard : walkGuard soko1_2.board support p 31 56 .southWest = true) : bonus 31 p ≤ bonus 56 p := by
  have certified := compare0 p (guard34 p guard)
  simpa only [at31, at56, Int.zero_add] using certified
theorem check34 (p : Pattern) : (!walkGuard soko1_2.board support p 31 56 .southWest || decide (bonus 31 p ≤ bonus 56 p)) = true :=
  check_of_implication _ _ (bound34 p)
theorem guard35 (p : Pattern) (guard : walkGuard soko1_2.board support p 32 33 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound35 (p : Pattern) (guard : walkGuard soko1_2.board support p 32 33 .east = true) : bonus 32 p ≤ bonus 33 p := by
  have certified := compare0 p (guard35 p guard)
  simpa only [at32, at33, Int.zero_add] using certified
theorem check35 (p : Pattern) : (!walkGuard soko1_2.board support p 32 33 .east || decide (bonus 32 p ≤ bonus 33 p)) = true :=
  check_of_implication _ _ (bound35 p)
theorem guard36 (p : Pattern) (guard : pushGuard support p 32 33 34 34 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound36 (p : Pattern) (guard : pushGuard support p 32 33 34 34 = true) : bonus 32 p ≤ 1 + Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.boulder 33 + bonus 33 (change p 33 (some 34)) := by
  have certified := compare3 p (guard36 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 33 (some 34))
  have normalized := agree75 _ _ (change_representative support p 33 (some 34) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check36 (p : Pattern) : (!pushGuard support p 32 33 34 34 || decide (bonus 32 p ≤ 1 + Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.boulder 33 + bonus 33 (change p 33 (some 34)))) = true :=
  check_of_implication _ _ (bound36 p)
theorem guard37 (p : Pattern) (guard : pushGuard support p 32 33 34 34 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound37 (p : Pattern) (guard : pushGuard support p 32 33 34 34 = true) : bonus 32 p ≤ 1 - Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.hole 34 + bonus 33 (change p 33 none) := by
  have certified := compare3 p (guard37 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 33 none)
  have normalized := agree75 _ _ (change_representative support p 33 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check37 (p : Pattern) : (!pushGuard support p 32 33 34 34 || decide (bonus 32 p ≤ 1 - Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.hole 34 + bonus 33 (change p 33 none))) = true :=
  check_of_implication _ _ (bound37 p)
theorem guard38 (p : Pattern) (guard : walkGuard soko1_2.board support p 32 31 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound38 (p : Pattern) (guard : walkGuard soko1_2.board support p 32 31 .west = true) : bonus 32 p ≤ bonus 31 p := by
  have certified := compare0 p (guard38 p guard)
  simpa only [at32, at31, Int.zero_add] using certified
theorem check38 (p : Pattern) : (!walkGuard soko1_2.board support p 32 31 .west || decide (bonus 32 p ≤ bonus 31 p)) = true :=
  check_of_implication _ _ (bound38 p)
theorem guard39 (p : Pattern) (guard : pushGuard support p 32 31 30 30 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound39 (p : Pattern) (guard : pushGuard support p 32 31 30 30 = true) : bonus 32 p ≤ 1 + Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.boulder 31 + bonus 31 (change p 31 (some 30)) := by
  have certified := compare3 p (guard39 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 31 (some 30))
  have normalized := agree75 _ _ (change_representative support p 31 (some 30) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check39 (p : Pattern) : (!pushGuard support p 32 31 30 30 || decide (bonus 32 p ≤ 1 + Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.boulder 31 + bonus 31 (change p 31 (some 30)))) = true :=
  check_of_implication _ _ (bound39 p)
theorem guard40 (p : Pattern) (guard : walkGuard soko1_2.board support p 33 34 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound40 (p : Pattern) (guard : walkGuard soko1_2.board support p 33 34 .east = true) : bonus 33 p ≤ bonus 34 p := by
  have certified := compare0 p (guard40 p guard)
  simpa only [at33, at34, Int.zero_add] using certified
theorem check40 (p : Pattern) : (!walkGuard soko1_2.board support p 33 34 .east || decide (bonus 33 p ≤ bonus 34 p)) = true :=
  check_of_implication _ _ (bound40 p)
theorem guard41 (p : Pattern) (guard : pushGuard support p 33 34 35 35 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound41 (p : Pattern) (guard : pushGuard support p 33 34 35 35 = true) : bonus 33 p ≤ 1 + Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.boulder 34 + bonus 34 (change p 34 (some 35)) := by
  have certified := compare3 p (guard41 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 34 (some 35))
  have normalized := agree75 _ _ (change_representative support p 34 (some 35) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check41 (p : Pattern) : (!pushGuard support p 33 34 35 35 || decide (bonus 33 p ≤ 1 + Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.boulder 34 + bonus 34 (change p 34 (some 35)))) = true :=
  check_of_implication _ _ (bound41 p)
theorem guard42 (p : Pattern) (guard : pushGuard support p 33 34 35 35 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound42 (p : Pattern) (guard : pushGuard support p 33 34 35 35 = true) : bonus 33 p ≤ 1 - Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.hole 35 + bonus 34 (change p 34 none) := by
  have certified := compare3 p (guard42 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 34 none)
  have normalized := agree75 _ _ (change_representative support p 34 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check42 (p : Pattern) : (!pushGuard support p 33 34 35 35 || decide (bonus 33 p ≤ 1 - Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.hole 35 + bonus 34 (change p 34 none))) = true :=
  check_of_implication _ _ (bound42 p)
theorem guard43 (p : Pattern) (guard : walkGuard soko1_2.board support p 33 32 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound43 (p : Pattern) (guard : walkGuard soko1_2.board support p 33 32 .west = true) : bonus 33 p ≤ bonus 32 p := by
  have certified := compare0 p (guard43 p guard)
  simpa only [at33, at32, Int.zero_add] using certified
theorem check43 (p : Pattern) : (!walkGuard soko1_2.board support p 33 32 .west || decide (bonus 33 p ≤ bonus 32 p)) = true :=
  check_of_implication _ _ (bound43 p)
theorem guard44 (p : Pattern) (guard : pushGuard support p 33 32 31 29 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound44 (p : Pattern) (guard : pushGuard support p 33 32 31 29 = true) : bonus 33 p ≤ 1 + Generated.soko1_2Potential.boulder 29 - Generated.soko1_2Potential.boulder 32 + bonus 32 (change p 32 (some 29)) := by
  have certified := compare4 p (guard44 p guard)
  change d75 p ≤ (19 : Int) + d75 (change p 32 (some 29))
  have normalized := agree75 _ _ (change_representative support p 32 (some 29) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (19 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check44 (p : Pattern) : (!pushGuard support p 33 32 31 29 || decide (bonus 33 p ≤ 1 + Generated.soko1_2Potential.boulder 29 - Generated.soko1_2Potential.boulder 32 + bonus 32 (change p 32 (some 29)))) = true :=
  check_of_implication _ _ (bound44 p)
theorem guard45 (p : Pattern) (guard : pushGuard support p 33 32 31 32 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound45 (p : Pattern) (guard : pushGuard support p 33 32 31 32 = true) : bonus 33 p ≤ 1 - Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.hole 32 + bonus 32 (change p 32 none) := by
  have certified := compare3 p (guard45 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 32 none)
  have normalized := agree75 _ _ (change_representative support p 32 none 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check45 (p : Pattern) : (!pushGuard support p 33 32 31 32 || decide (bonus 33 p ≤ 1 - Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.hole 32 + bonus 32 (change p 32 none))) = true :=
  check_of_implication _ _ (bound45 p)
theorem guard46 (p : Pattern) (guard : walkGuard soko1_2.board support p 34 35 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound46 (p : Pattern) (guard : walkGuard soko1_2.board support p 34 35 .east = true) : bonus 34 p ≤ bonus 35 p := by
  have certified := compare0 p (guard46 p guard)
  simpa only [at34, at35, Int.zero_add] using certified
theorem check46 (p : Pattern) : (!walkGuard soko1_2.board support p 34 35 .east || decide (bonus 34 p ≤ bonus 35 p)) = true :=
  check_of_implication _ _ (bound46 p)
theorem guard47 (p : Pattern) (guard : pushGuard support p 34 35 36 36 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound47 (p : Pattern) (guard : pushGuard support p 34 35 36 36 = true) : bonus 34 p ≤ 1 + Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.boulder 35 + bonus 35 (change p 35 (some 36)) := by
  have certified := compare3 p (guard47 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 35 (some 36))
  have normalized := agree75 _ _ (change_representative support p 35 (some 36) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check47 (p : Pattern) : (!pushGuard support p 34 35 36 36 || decide (bonus 34 p ≤ 1 + Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.boulder 35 + bonus 35 (change p 35 (some 36)))) = true :=
  check_of_implication _ _ (bound47 p)
end NetHack.Sokoban12CostPartition
