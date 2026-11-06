import NetHack.Sokoban32Refined.ActionBounds000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard24 (p : Pattern) (guard : pushGuard support p 44 45 46 46 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound24 (p : Pattern) (guard : pushGuard support p 44 45 46 46 = true) : bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder 46 - Generated.soko3_2Potential.boulder 45 + bonus 45 (change p 45 (some 46)) := by
  have certified := compare37 p (guard24 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 45 (some 46))
  have normalized := agree0 _ _ (change_representative support p 45 (some 46) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check24 (p : Pattern) : (!pushGuard support p 44 45 46 46 || decide (bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder 46 - Generated.soko3_2Potential.boulder 45 + bonus 45 (change p 45 (some 46)))) = true :=
  check_of_implication _ _ (bound24 p)
theorem guard25 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 43 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound25 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 43 .west = true) : bonus 44 p ≤ bonus 43 p := by
  have certified := compare103 p (guard25 p guard)
  simpa only [at44, at43, Int.zero_add] using certified
theorem check25 (p : Pattern) : (!walkGuard soko3_2.board support p 44 43 .west || decide (bonus 44 p ≤ bonus 43 p)) = true :=
  check_of_implication _ _ (bound25 p)
theorem guard26 (p : Pattern) (guard : pushGuard support p 44 43 42 42 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound26 (p : Pattern) (guard : pushGuard support p 44 43 42 42 = true) : bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder 42 - Generated.soko3_2Potential.boulder 43 + bonus 43 (change p 43 (some 42)) := by
  have certified := compare37 p (guard26 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 43 (some 42))
  have normalized := agree0 _ _ (change_representative support p 43 (some 42) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check26 (p : Pattern) : (!pushGuard support p 44 43 42 42 || decide (bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder 42 - Generated.soko3_2Potential.boulder 43 + bonus 43 (change p 43 (some 42)))) = true :=
  check_of_implication _ _ (bound26 p)
theorem guard27 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 71 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound27 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 71 .southEast = true) : bonus 44 p ≤ bonus 71 p := by
  have certified := compare103 p (guard27 p guard)
  simpa only [at44, at71, Int.zero_add] using certified
theorem check27 (p : Pattern) : (!walkGuard soko3_2.board support p 44 71 .southEast || decide (bonus 44 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound27 p)
theorem guard28 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 69 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound28 (p : Pattern) (guard : walkGuard soko3_2.board support p 44 69 .southWest = true) : bonus 44 p ≤ bonus 69 p := by
  have certified := compare103 p (guard28 p guard)
  simpa only [at44, at69, Int.zero_add] using certified
theorem check28 (p : Pattern) : (!walkGuard soko3_2.board support p 44 69 .southWest || decide (bonus 44 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound28 p)
theorem guard29 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 71 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound29 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 71 .south = true) : bonus 45 p ≤ bonus 71 p := by
  have certified := compare103 p (guard29 p guard)
  simpa only [at45, at71, Int.zero_add] using certified
theorem check29 (p : Pattern) : (!walkGuard soko3_2.board support p 45 71 .south || decide (bonus 45 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound29 p)
theorem guard30 (p : Pattern) (guard : pushGuard support p 45 71 97 97 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound30 (p : Pattern) (guard : pushGuard support p 45 71 97 97 = true) : bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some 97)) := by
  have certified := compare37 p (guard30 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 71 (some 97))
  have normalized := agree0 _ _ (change_representative support p 71 (some 97) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check30 (p : Pattern) : (!pushGuard support p 45 71 97 97 || decide (bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some 97)))) = true :=
  check_of_implication _ _ (bound30 p)
theorem guard31 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 46 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound31 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 46 .east = true) : bonus 45 p ≤ bonus 46 p := by
  have certified := compare103 p (guard31 p guard)
  simpa only [at45, at46, Int.zero_add] using certified
theorem check31 (p : Pattern) : (!walkGuard soko3_2.board support p 45 46 .east || decide (bonus 45 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound31 p)
theorem guard32 (p : Pattern) (guard : pushGuard support p 45 46 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound32 (p : Pattern) (guard : pushGuard support p 45 46 47 47 = true) : bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder 47 - Generated.soko3_2Potential.boulder 46 + bonus 46 (change p 46 (some 47)) := by
  have certified := compare37 p (guard32 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 46 (some 47))
  have normalized := agree0 _ _ (change_representative support p 46 (some 47) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check32 (p : Pattern) : (!pushGuard support p 45 46 47 47 || decide (bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder 47 - Generated.soko3_2Potential.boulder 46 + bonus 46 (change p 46 (some 47)))) = true :=
  check_of_implication _ _ (bound32 p)
theorem guard33 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 44 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound33 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 44 .west = true) : bonus 45 p ≤ bonus 44 p := by
  have certified := compare103 p (guard33 p guard)
  simpa only [at45, at44, Int.zero_add] using certified
theorem check33 (p : Pattern) : (!walkGuard soko3_2.board support p 45 44 .west || decide (bonus 45 p ≤ bonus 44 p)) = true :=
  check_of_implication _ _ (bound33 p)
theorem guard34 (p : Pattern) (guard : pushGuard support p 45 44 43 43 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound34 (p : Pattern) (guard : pushGuard support p 45 44 43 43 = true) : bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder 43 - Generated.soko3_2Potential.boulder 44 + bonus 44 (change p 44 (some 43)) := by
  have certified := compare37 p (guard34 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 44 (some 43))
  have normalized := agree0 _ _ (change_representative support p 44 (some 43) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check34 (p : Pattern) : (!pushGuard support p 45 44 43 43 || decide (bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder 43 - Generated.soko3_2Potential.boulder 44 + bonus 44 (change p 44 (some 43)))) = true :=
  check_of_implication _ _ (bound34 p)
theorem guard35 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 72 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound35 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 72 .southEast = true) : bonus 45 p ≤ bonus 72 p := by
  have certified := compare103 p (guard35 p guard)
  simpa only [at45, at72, Int.zero_add] using certified
theorem check35 (p : Pattern) : (!walkGuard soko3_2.board support p 45 72 .southEast || decide (bonus 45 p ≤ bonus 72 p)) = true :=
  check_of_implication _ _ (bound35 p)
theorem guard36 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 70 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound36 (p : Pattern) (guard : walkGuard soko3_2.board support p 45 70 .southWest = true) : bonus 45 p ≤ bonus 70 p := by
  have certified := compare103 p (guard36 p guard)
  simpa only [at45, at70, Int.zero_add] using certified
theorem check36 (p : Pattern) : (!walkGuard soko3_2.board support p 45 70 .southWest || decide (bonus 45 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound36 p)
theorem guard37 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 72 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound37 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 72 .south = true) : bonus 46 p ≤ bonus 72 p := by
  have certified := compare103 p (guard37 p guard)
  simpa only [at46, at72, Int.zero_add] using certified
theorem check37 (p : Pattern) : (!walkGuard soko3_2.board support p 46 72 .south || decide (bonus 46 p ≤ bonus 72 p)) = true :=
  check_of_implication _ _ (bound37 p)
theorem guard38 (p : Pattern) (guard : pushGuard support p 46 72 98 98 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound38 (p : Pattern) (guard : pushGuard support p 46 72 98 98 = true) : bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some 98)) := by
  have certified := compare37 p (guard38 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 72 (some 98))
  have normalized := agree0 _ _ (change_representative support p 72 (some 98) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check38 (p : Pattern) : (!pushGuard support p 46 72 98 98 || decide (bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some 98)))) = true :=
  check_of_implication _ _ (bound38 p)
theorem guard39 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 47 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound39 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 47 .east = true) : bonus 46 p ≤ bonus 47 p := by
  have certified := compare103 p (guard39 p guard)
  simpa only [at46, at47, Int.zero_add] using certified
theorem check39 (p : Pattern) : (!walkGuard soko3_2.board support p 46 47 .east || decide (bonus 46 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound39 p)
theorem guard40 (p : Pattern) (guard : pushGuard support p 46 47 48 48 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound40 (p : Pattern) (guard : pushGuard support p 46 47 48 48 = true) : bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder 48 - Generated.soko3_2Potential.boulder 47 + bonus 47 (change p 47 (some 48)) := by
  have certified := compare37 p (guard40 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 47 (some 48))
  have normalized := agree0 _ _ (change_representative support p 47 (some 48) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check40 (p : Pattern) : (!pushGuard support p 46 47 48 48 || decide (bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder 48 - Generated.soko3_2Potential.boulder 47 + bonus 47 (change p 47 (some 48)))) = true :=
  check_of_implication _ _ (bound40 p)
theorem guard41 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 45 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound41 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 45 .west = true) : bonus 46 p ≤ bonus 45 p := by
  have certified := compare103 p (guard41 p guard)
  simpa only [at46, at45, Int.zero_add] using certified
theorem check41 (p : Pattern) : (!walkGuard soko3_2.board support p 46 45 .west || decide (bonus 46 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound41 p)
theorem guard42 (p : Pattern) (guard : pushGuard support p 46 45 44 44 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound42 (p : Pattern) (guard : pushGuard support p 46 45 44 44 = true) : bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder 44 - Generated.soko3_2Potential.boulder 45 + bonus 45 (change p 45 (some 44)) := by
  have certified := compare37 p (guard42 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 45 (some 44))
  have normalized := agree0 _ _ (change_representative support p 45 (some 44) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check42 (p : Pattern) : (!pushGuard support p 46 45 44 44 || decide (bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder 44 - Generated.soko3_2Potential.boulder 45 + bonus 45 (change p 45 (some 44)))) = true :=
  check_of_implication _ _ (bound42 p)
theorem guard43 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 73 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound43 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 73 .southEast = true) : bonus 46 p ≤ bonus 73 p := by
  have certified := compare103 p (guard43 p guard)
  simpa only [at46, at73, Int.zero_add] using certified
theorem check43 (p : Pattern) : (!walkGuard soko3_2.board support p 46 73 .southEast || decide (bonus 46 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound43 p)
theorem guard44 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 71 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound44 (p : Pattern) (guard : walkGuard soko3_2.board support p 46 71 .southWest = true) : bonus 46 p ≤ bonus 71 p := by
  have certified := compare103 p (guard44 p guard)
  simpa only [at46, at71, Int.zero_add] using certified
theorem check44 (p : Pattern) : (!walkGuard soko3_2.board support p 46 71 .southWest || decide (bonus 46 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound44 p)
theorem guard45 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 73 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound45 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 73 .south = true) : bonus 47 p ≤ bonus 73 p := by
  have certified := compare103 p (guard45 p guard)
  simpa only [at47, at73, Int.zero_add] using certified
theorem check45 (p : Pattern) : (!walkGuard soko3_2.board support p 47 73 .south || decide (bonus 47 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound45 p)
theorem guard46 (p : Pattern) (guard : pushGuard support p 47 73 99 99 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound46 (p : Pattern) (guard : pushGuard support p 47 73 99 99 = true) : bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some 99)) := by
  have certified := compare37 p (guard46 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 73 (some 99))
  have normalized := agree0 _ _ (change_representative support p 73 (some 99) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check46 (p : Pattern) : (!pushGuard support p 47 73 99 99 || decide (bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some 99)))) = true :=
  check_of_implication _ _ (bound46 p)
theorem guard47 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 48 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound47 (p : Pattern) (guard : walkGuard soko3_2.board support p 47 48 .east = true) : bonus 47 p ≤ bonus 48 p := by
  have certified := compare103 p (guard47 p guard)
  simpa only [at47, at48, Int.zero_add] using certified
theorem check47 (p : Pattern) : (!walkGuard soko3_2.board support p 47 48 .east || decide (bonus 47 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound47 p)
end NetHack.Sokoban32Refined
