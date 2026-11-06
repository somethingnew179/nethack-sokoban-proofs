import NetHack.Sokoban22Refined85.ActionBounds000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard24 (p : Pattern) (guard : pushGuard support p 30 52 74 74 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound24 (p : Pattern) (guard : pushGuard support p 30 52 74 74 = true) : bonus 30 p ≤ 1 + Generated.soko2_2Potential.boulder 74 - Generated.soko2_2Potential.boulder 52 + bonus 52 (change p 52 (some 74)) := by
  have certified := compare20 p (guard24 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 52 (some 74))
  have normalized := agree312 _ _ (change_representative support p 52 (some 74) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check24 (p : Pattern) : (!pushGuard support p 30 52 74 74 || decide (bonus 30 p ≤ 1 + Generated.soko2_2Potential.boulder 74 - Generated.soko2_2Potential.boulder 52 + bonus 52 (change p 52 (some 74)))) = true :=
  check_of_implication _ _ (bound24 p)
theorem guard25 (p : Pattern) (guard : walkGuard soko2_2.board support p 30 29 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound25 (p : Pattern) (guard : walkGuard soko2_2.board support p 30 29 .west = true) : bonus 30 p ≤ bonus 29 p := by
  have certified := compare19 p (guard25 p guard)
  simpa only [at30, at29, Int.zero_add] using certified
theorem check25 (p : Pattern) : (!walkGuard soko2_2.board support p 30 29 .west || decide (bonus 30 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound25 p)
theorem guard26 (p : Pattern) (guard : pushGuard support p 30 29 28 28 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound26 (p : Pattern) (guard : pushGuard support p 30 29 28 28 = true) : bonus 30 p ≤ 1 + Generated.soko2_2Potential.boulder 28 - Generated.soko2_2Potential.boulder 29 + bonus 29 (change p 29 (some 28)) := by
  have certified := compare20 p (guard26 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 29 (some 28))
  have normalized := agree312 _ _ (change_representative support p 29 (some 28) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check26 (p : Pattern) : (!pushGuard support p 30 29 28 28 || decide (bonus 30 p ≤ 1 + Generated.soko2_2Potential.boulder 28 - Generated.soko2_2Potential.boulder 29 + bonus 29 (change p 29 (some 28)))) = true :=
  check_of_implication _ _ (bound26 p)
theorem guard27 (p : Pattern) (guard : walkGuard soko2_2.board support p 30 51 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound27 (p : Pattern) (guard : walkGuard soko2_2.board support p 30 51 .southWest = true) : bonus 30 p ≤ bonus 51 p := by
  have certified := compare19 p (guard27 p guard)
  simpa only [at30, at51, Int.zero_add] using certified
theorem check27 (p : Pattern) : (!walkGuard soko2_2.board support p 30 51 .southWest || decide (bonus 30 p ≤ bonus 51 p)) = true :=
  check_of_implication _ _ (bound27 p)
theorem guard28 (p : Pattern) (guard : walkGuard soko2_2.board support p 45 67 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound28 (p : Pattern) (guard : walkGuard soko2_2.board support p 45 67 .south = true) : bonus 45 p ≤ bonus 67 p := by
  have certified := compare0 p (guard28 p guard)
  simpa only [at45, at67, Int.zero_add] using certified
theorem check28 (p : Pattern) : (!walkGuard soko2_2.board support p 45 67 .south || decide (bonus 45 p ≤ bonus 67 p)) = true :=
  check_of_implication _ _ (bound28 p)
theorem guard29 (p : Pattern) (guard : pushGuard support p 45 67 89 89 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound29 (p : Pattern) (guard : pushGuard support p 45 67 89 89 = true) : bonus 45 p ≤ 1 + Generated.soko2_2Potential.boulder 89 - Generated.soko2_2Potential.boulder 67 + bonus 67 (change p 67 (some 89)) := by
  have certified := compare1 p (guard29 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 67 (some 89))
  have normalized := agree267 _ _ (change_representative support p 67 (some 89) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check29 (p : Pattern) : (!pushGuard support p 45 67 89 89 || decide (bonus 45 p ≤ 1 + Generated.soko2_2Potential.boulder 89 - Generated.soko2_2Potential.boulder 67 + bonus 67 (change p 67 (some 89)))) = true :=
  check_of_implication _ _ (bound29 p)
theorem guard30 (p : Pattern) (guard : walkGuard soko2_2.board support p 45 46 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound30 (p : Pattern) (guard : walkGuard soko2_2.board support p 45 46 .east = true) : bonus 45 p ≤ bonus 46 p := by
  have certified := compare0 p (guard30 p guard)
  simpa only [at45, at46, Int.zero_add] using certified
theorem check30 (p : Pattern) : (!walkGuard soko2_2.board support p 45 46 .east || decide (bonus 45 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound30 p)
theorem guard31 (p : Pattern) (guard : pushGuard support p 45 46 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound31 (p : Pattern) (guard : pushGuard support p 45 46 47 47 = true) : bonus 45 p ≤ 1 + Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.boulder 46 + bonus 46 (change p 46 (some 47)) := by
  have certified := compare1 p (guard31 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 46 (some 47))
  have normalized := agree267 _ _ (change_representative support p 46 (some 47) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check31 (p : Pattern) : (!pushGuard support p 45 46 47 47 || decide (bonus 45 p ≤ 1 + Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.boulder 46 + bonus 46 (change p 46 (some 47)))) = true :=
  check_of_implication _ _ (bound31 p)
theorem guard32 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 47 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound32 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 47 .east = true) : bonus 46 p ≤ bonus 47 p := by
  have certified := compare0 p (guard32 p guard)
  simpa only [at46, at47, Int.zero_add] using certified
theorem check32 (p : Pattern) : (!walkGuard soko2_2.board support p 46 47 .east || decide (bonus 46 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound32 p)
theorem guard33 (p : Pattern) (guard : pushGuard support p 46 47 48 48 = true) : d4038 p = 1 := by
  change (!false && (!false || false) && !(p 48) && (!(p 48) || false)) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound33 (p : Pattern) (guard : pushGuard support p 46 47 48 48 = true) : bonus 46 p ≤ 1 + Generated.soko2_2Potential.boulder 48 - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some 48)) := by
  have certified := compare268 p (guard33 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 47 (some 48))
  have normalized := agree267 _ _ (change_representative support p 47 (some 48) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 (some 48))
  rw [sub660]
  exact certified
theorem check33 (p : Pattern) : (!pushGuard support p 46 47 48 48 || decide (bonus 46 p ≤ 1 + Generated.soko2_2Potential.boulder 48 - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some 48)))) = true :=
  check_of_implication _ _ (bound33 p)
theorem guard34 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 45 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound34 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 45 .west = true) : bonus 46 p ≤ bonus 45 p := by
  have certified := compare0 p (guard34 p guard)
  simpa only [at46, at45, Int.zero_add] using certified
theorem check34 (p : Pattern) : (!walkGuard soko2_2.board support p 46 45 .west || decide (bonus 46 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound34 p)
theorem guard35 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 25 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound35 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 25 .northEast = true) : bonus 46 p ≤ bonus 25 p := by
  have certified := compare0 p (guard35 p guard)
  simpa only [at46, at25, Int.zero_add] using certified
theorem check35 (p : Pattern) : (!walkGuard soko2_2.board support p 46 25 .northEast || decide (bonus 46 p ≤ bonus 25 p)) = true :=
  check_of_implication _ _ (bound35 p)
theorem guard36 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 69 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound36 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 69 .southEast = true) : bonus 46 p ≤ bonus 69 p := by
  have certified := compare0 p (guard36 p guard)
  simpa only [at46, at69, Int.zero_add] using certified
theorem check36 (p : Pattern) : (!walkGuard soko2_2.board support p 46 69 .southEast || decide (bonus 46 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound36 p)
theorem guard37 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 67 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound37 (p : Pattern) (guard : walkGuard soko2_2.board support p 46 67 .southWest = true) : bonus 46 p ≤ bonus 67 p := by
  have certified := compare0 p (guard37 p guard)
  simpa only [at46, at67, Int.zero_add] using certified
theorem check37 (p : Pattern) : (!walkGuard soko2_2.board support p 46 67 .southWest || decide (bonus 46 p ≤ bonus 67 p)) = true :=
  check_of_implication _ _ (bound37 p)
theorem guard38 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 25 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound38 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 25 .north = true) : bonus 47 p ≤ bonus 25 p := by
  have certified := compare0 p (guard38 p guard)
  simpa only [at47, at25, Int.zero_add] using certified
theorem check38 (p : Pattern) : (!walkGuard soko2_2.board support p 47 25 .north || decide (bonus 47 p ≤ bonus 25 p)) = true :=
  check_of_implication _ _ (bound38 p)
theorem guard39 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 69 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound39 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 69 .south = true) : bonus 47 p ≤ bonus 69 p := by
  have certified := compare0 p (guard39 p guard)
  simpa only [at47, at69, Int.zero_add] using certified
theorem check39 (p : Pattern) : (!walkGuard soko2_2.board support p 47 69 .south || decide (bonus 47 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound39 p)
theorem guard40 (p : Pattern) (guard : pushGuard support p 47 69 91 91 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound40 (p : Pattern) (guard : pushGuard support p 47 69 91 91 = true) : bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder 91 - Generated.soko2_2Potential.boulder 69 + bonus 69 (change p 69 (some 91)) := by
  have certified := compare1 p (guard40 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 69 (some 91))
  have normalized := agree267 _ _ (change_representative support p 69 (some 91) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check40 (p : Pattern) : (!pushGuard support p 47 69 91 91 || decide (bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder 91 - Generated.soko2_2Potential.boulder 69 + bonus 69 (change p 69 (some 91)))) = true :=
  check_of_implication _ _ (bound40 p)
theorem guard41 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 48 .east = true) : d4038 p = 1 := by
  change (!false && !(p 48) && !false) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound41 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 48 .east = true) : bonus 47 p ≤ bonus 48 p := by
  have certified := compare4 p (guard41 p guard)
  simpa only [at47, at48, Int.zero_add] using certified
theorem check41 (p : Pattern) : (!walkGuard soko2_2.board support p 47 48 .east || decide (bonus 47 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound41 p)
theorem guard42 (p : Pattern) (guard : pushGuard support p 47 48 49 49 = true) : d4045 p = 1 := by
  change (!false && (!true || (p 48)) && !(p 49) && (!(p 49) || false)) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49
  all_goals simp [d0, d1, d4040, d4045, h48, h49] at guard ⊢
theorem bound42 (p : Pattern) (guard : pushGuard support p 47 48 49 49 = true) : bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.boulder 48 + bonus 48 (change p 48 (some 49)) := by
  have certified := compare436 p (guard42 p guard)
  change d267 p ≤ (1 : Int) + d481 (change p 48 (some 49))
  have normalized := agree481 _ _ (change_representative support p 48 (some 49) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d481 (change p 48 (some 49))
  rw [sub830]
  exact certified
theorem check42 (p : Pattern) : (!pushGuard support p 47 48 49 49 || decide (bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.boulder 48 + bonus 48 (change p 48 (some 49)))) = true :=
  check_of_implication _ _ (bound42 p)
theorem guard43 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 46 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound43 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 46 .west = true) : bonus 47 p ≤ bonus 46 p := by
  have certified := compare0 p (guard43 p guard)
  simpa only [at47, at46, Int.zero_add] using certified
theorem check43 (p : Pattern) : (!walkGuard soko2_2.board support p 47 46 .west || decide (bonus 47 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound43 p)
theorem guard44 (p : Pattern) (guard : pushGuard support p 47 46 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound44 (p : Pattern) (guard : pushGuard support p 47 46 45 45 = true) : bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder 45 - Generated.soko2_2Potential.boulder 46 + bonus 46 (change p 46 (some 45)) := by
  have certified := compare1 p (guard44 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 46 (some 45))
  have normalized := agree267 _ _ (change_representative support p 46 (some 45) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check44 (p : Pattern) : (!pushGuard support p 47 46 45 45 || decide (bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder 45 - Generated.soko2_2Potential.boulder 46 + bonus 46 (change p 46 (some 45)))) = true :=
  check_of_implication _ _ (bound44 p)
theorem guard45 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 70 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 48))) = true at guard
  cases h48 : p 48
  all_goals simp [d1, h48] at guard ⊢
theorem bound45 (p : Pattern) (guard : walkGuard soko2_2.board support p 47 70 .southEast = true) : bonus 47 p ≤ bonus 70 p := by
  have certified := compare0 p (guard45 p guard)
  simpa only [at47, at70, Int.zero_add] using certified
theorem check45 (p : Pattern) : (!walkGuard soko2_2.board support p 47 70 .southEast || decide (bonus 47 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound45 p)
theorem guard46 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 70 .south = true) : d4038 p = 1 := by
  change (!(p 48) && !false && !false) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound46 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 70 .south = true) : bonus 48 p ≤ bonus 70 p := by
  have certified := compare438 p (guard46 p guard)
  simpa only [at48, at70, Int.zero_add] using certified
theorem check46 (p : Pattern) : (!walkGuard soko2_2.board support p 48 70 .south || decide (bonus 48 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound46 p)
theorem guard47 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 49 .east = true) : d4044 p = 1 := by
  change (!(p 48) && !(p 49) && !false) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49
  all_goals simp [d0, d1, d4040, d4044, h48, h49] at guard ⊢
theorem bound47 (p : Pattern) (guard : walkGuard soko2_2.board support p 48 49 .east = true) : bonus 48 p ≤ bonus 49 p := by
  have certified := compare440 p (guard47 p guard)
  simpa only [at48, at49, Int.zero_add] using certified
theorem check47 (p : Pattern) : (!walkGuard soko2_2.board support p 48 49 .east || decide (bonus 48 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound47 p)
end NetHack.Sokoban22Refined85
