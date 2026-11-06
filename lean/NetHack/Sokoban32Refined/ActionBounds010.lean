import NetHack.Sokoban32Refined.ActionBounds009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard240 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 68 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound240 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 68 .north = true) : bonus 94 p ≤ bonus 68 p := by
  have certified := compare103 p (guard240 p guard)
  simpa only [at94, at68, Int.zero_add] using certified
theorem check240 (p : Pattern) : (!walkGuard soko3_2.board support p 94 68 .north || decide (bonus 94 p ≤ bonus 68 p)) = true :=
  check_of_implication _ _ (bound240 p)
theorem guard241 (p : Pattern) (guard : pushGuard support p 94 68 42 42 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound241 (p : Pattern) (guard : pushGuard support p 94 68 42 42 = true) : bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder 42 - Generated.soko3_2Potential.boulder 68 + bonus 68 (change p 68 (some 42)) := by
  have certified := compare37 p (guard241 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 68 (some 42))
  have normalized := agree0 _ _ (change_representative support p 68 (some 42) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check241 (p : Pattern) : (!pushGuard support p 94 68 42 42 || decide (bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder 42 - Generated.soko3_2Potential.boulder 68 + bonus 68 (change p 68 (some 42)))) = true :=
  check_of_implication _ _ (bound241 p)
theorem guard242 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 120 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound242 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 120 .south = true) : bonus 94 p ≤ bonus 120 p := by
  have certified := compare103 p (guard242 p guard)
  simpa only [at94, at120, Int.zero_add] using certified
theorem check242 (p : Pattern) : (!walkGuard soko3_2.board support p 94 120 .south || decide (bonus 94 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound242 p)
theorem guard243 (p : Pattern) (guard : pushGuard support p 94 120 146 146 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound243 (p : Pattern) (guard : pushGuard support p 94 120 146 146 = true) : bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder 146 - Generated.soko3_2Potential.boulder 120 + bonus 120 (change p 120 (some 146)) := by
  have certified := compare37 p (guard243 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 120 (some 146))
  have normalized := agree0 _ _ (change_representative support p 120 (some 146) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check243 (p : Pattern) : (!pushGuard support p 94 120 146 146 || decide (bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder 146 - Generated.soko3_2Potential.boulder 120 + bonus 120 (change p 120 (some 146)))) = true :=
  check_of_implication _ _ (bound243 p)
theorem guard244 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 95 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound244 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 95 .east = true) : bonus 94 p ≤ bonus 95 p := by
  have certified := compare103 p (guard244 p guard)
  simpa only [at94, at95, Int.zero_add] using certified
theorem check244 (p : Pattern) : (!walkGuard soko3_2.board support p 94 95 .east || decide (bonus 94 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound244 p)
theorem guard245 (p : Pattern) (guard : pushGuard support p 94 95 96 96 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound245 (p : Pattern) (guard : pushGuard support p 94 95 96 96 = true) : bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some 96)) := by
  have certified := compare37 p (guard245 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 95 (some 96))
  have normalized := agree0 _ _ (change_representative support p 95 (some 96) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check245 (p : Pattern) : (!pushGuard support p 94 95 96 96 || decide (bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some 96)))) = true :=
  check_of_implication _ _ (bound245 p)
theorem guard246 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 69 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound246 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 69 .northEast = true) : bonus 94 p ≤ bonus 69 p := by
  have certified := compare103 p (guard246 p guard)
  simpa only [at94, at69, Int.zero_add] using certified
theorem check246 (p : Pattern) : (!walkGuard soko3_2.board support p 94 69 .northEast || decide (bonus 94 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound246 p)
theorem guard247 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 121 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound247 (p : Pattern) (guard : walkGuard soko3_2.board support p 94 121 .southEast = true) : bonus 94 p ≤ bonus 121 p := by
  have certified := compare103 p (guard247 p guard)
  simpa only [at94, at121, Int.zero_add] using certified
theorem check247 (p : Pattern) : (!walkGuard soko3_2.board support p 94 121 .southEast || decide (bonus 94 p ≤ bonus 121 p)) = true :=
  check_of_implication _ _ (bound247 p)
theorem guard248 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 69 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound248 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 69 .north = true) : bonus 95 p ≤ bonus 69 p := by
  have certified := compare103 p (guard248 p guard)
  simpa only [at95, at69, Int.zero_add] using certified
theorem check248 (p : Pattern) : (!walkGuard soko3_2.board support p 95 69 .north || decide (bonus 95 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound248 p)
theorem guard249 (p : Pattern) (guard : pushGuard support p 95 69 43 43 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound249 (p : Pattern) (guard : pushGuard support p 95 69 43 43 = true) : bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder 43 - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some 43)) := by
  have certified := compare37 p (guard249 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 69 (some 43))
  have normalized := agree0 _ _ (change_representative support p 69 (some 43) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check249 (p : Pattern) : (!pushGuard support p 95 69 43 43 || decide (bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder 43 - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some 43)))) = true :=
  check_of_implication _ _ (bound249 p)
theorem guard250 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 121 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound250 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 121 .south = true) : bonus 95 p ≤ bonus 121 p := by
  have certified := compare103 p (guard250 p guard)
  simpa only [at95, at121, Int.zero_add] using certified
theorem check250 (p : Pattern) : (!walkGuard soko3_2.board support p 95 121 .south || decide (bonus 95 p ≤ bonus 121 p)) = true :=
  check_of_implication _ _ (bound250 p)
theorem guard251 (p : Pattern) (guard : pushGuard support p 95 121 147 147 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound251 (p : Pattern) (guard : pushGuard support p 95 121 147 147 = true) : bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some 147)) := by
  have certified := compare37 p (guard251 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 121 (some 147))
  have normalized := agree0 _ _ (change_representative support p 121 (some 147) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check251 (p : Pattern) : (!pushGuard support p 95 121 147 147 || decide (bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some 147)))) = true :=
  check_of_implication _ _ (bound251 p)
theorem guard252 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 96 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound252 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 96 .east = true) : bonus 95 p ≤ bonus 96 p := by
  have certified := compare103 p (guard252 p guard)
  simpa only [at95, at96, Int.zero_add] using certified
theorem check252 (p : Pattern) : (!walkGuard soko3_2.board support p 95 96 .east || decide (bonus 95 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound252 p)
theorem guard253 (p : Pattern) (guard : pushGuard support p 95 96 97 97 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound253 (p : Pattern) (guard : pushGuard support p 95 96 97 97 = true) : bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some 97)) := by
  have certified := compare37 p (guard253 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 96 (some 97))
  have normalized := agree0 _ _ (change_representative support p 96 (some 97) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check253 (p : Pattern) : (!pushGuard support p 95 96 97 97 || decide (bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some 97)))) = true :=
  check_of_implication _ _ (bound253 p)
theorem guard254 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 94 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound254 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 94 .west = true) : bonus 95 p ≤ bonus 94 p := by
  have certified := compare103 p (guard254 p guard)
  simpa only [at95, at94, Int.zero_add] using certified
theorem check254 (p : Pattern) : (!walkGuard soko3_2.board support p 95 94 .west || decide (bonus 95 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound254 p)
theorem guard255 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 70 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound255 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 70 .northEast = true) : bonus 95 p ≤ bonus 70 p := by
  have certified := compare103 p (guard255 p guard)
  simpa only [at95, at70, Int.zero_add] using certified
theorem check255 (p : Pattern) : (!walkGuard soko3_2.board support p 95 70 .northEast || decide (bonus 95 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound255 p)
theorem guard256 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 68 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound256 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 68 .northWest = true) : bonus 95 p ≤ bonus 68 p := by
  have certified := compare103 p (guard256 p guard)
  simpa only [at95, at68, Int.zero_add] using certified
theorem check256 (p : Pattern) : (!walkGuard soko3_2.board support p 95 68 .northWest || decide (bonus 95 p ≤ bonus 68 p)) = true :=
  check_of_implication _ _ (bound256 p)
theorem guard257 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 122 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound257 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 122 .southEast = true) : bonus 95 p ≤ bonus 122 p := by
  have certified := compare103 p (guard257 p guard)
  simpa only [at95, at122, Int.zero_add] using certified
theorem check257 (p : Pattern) : (!walkGuard soko3_2.board support p 95 122 .southEast || decide (bonus 95 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound257 p)
theorem guard258 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 120 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound258 (p : Pattern) (guard : walkGuard soko3_2.board support p 95 120 .southWest = true) : bonus 95 p ≤ bonus 120 p := by
  have certified := compare103 p (guard258 p guard)
  simpa only [at95, at120, Int.zero_add] using certified
theorem check258 (p : Pattern) : (!walkGuard soko3_2.board support p 95 120 .southWest || decide (bonus 95 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound258 p)
theorem guard259 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 70 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound259 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 70 .north = true) : bonus 96 p ≤ bonus 70 p := by
  have certified := compare103 p (guard259 p guard)
  simpa only [at96, at70, Int.zero_add] using certified
theorem check259 (p : Pattern) : (!walkGuard soko3_2.board support p 96 70 .north || decide (bonus 96 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound259 p)
theorem guard260 (p : Pattern) (guard : pushGuard support p 96 70 44 44 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound260 (p : Pattern) (guard : pushGuard support p 96 70 44 44 = true) : bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder 44 - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some 44)) := by
  have certified := compare37 p (guard260 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 70 (some 44))
  have normalized := agree0 _ _ (change_representative support p 70 (some 44) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check260 (p : Pattern) : (!pushGuard support p 96 70 44 44 || decide (bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder 44 - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some 44)))) = true :=
  check_of_implication _ _ (bound260 p)
theorem guard261 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 122 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound261 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 122 .south = true) : bonus 96 p ≤ bonus 122 p := by
  have certified := compare103 p (guard261 p guard)
  simpa only [at96, at122, Int.zero_add] using certified
theorem check261 (p : Pattern) : (!walkGuard soko3_2.board support p 96 122 .south || decide (bonus 96 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound261 p)
theorem guard262 (p : Pattern) (guard : pushGuard support p 96 122 148 148 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound262 (p : Pattern) (guard : pushGuard support p 96 122 148 148 = true) : bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some 148)) := by
  have certified := compare37 p (guard262 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 122 (some 148))
  have normalized := agree0 _ _ (change_representative support p 122 (some 148) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check262 (p : Pattern) : (!pushGuard support p 96 122 148 148 || decide (bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some 148)))) = true :=
  check_of_implication _ _ (bound262 p)
theorem guard263 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 97 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound263 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 97 .east = true) : bonus 96 p ≤ bonus 97 p := by
  have certified := compare103 p (guard263 p guard)
  simpa only [at96, at97, Int.zero_add] using certified
theorem check263 (p : Pattern) : (!walkGuard soko3_2.board support p 96 97 .east || decide (bonus 96 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound263 p)
end NetHack.Sokoban32Refined
