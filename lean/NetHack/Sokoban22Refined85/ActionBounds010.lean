import NetHack.Sokoban22Refined85.ActionBounds009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard240 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 119 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound240 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 119 .south = true) : bonus 97 p ≤ bonus 119 p := by
  have certified := compare19 p (guard240 p guard)
  simpa only [at97, at119, Int.zero_add] using certified
theorem check240 (p : Pattern) : (!walkGuard soko2_2.board support p 97 119 .south || decide (bonus 97 p ≤ bonus 119 p)) = true :=
  check_of_implication _ _ (bound240 p)
theorem guard241 (p : Pattern) (guard : pushGuard support p 97 119 141 141 = true) : d4077 p = 1 := by
  change (!false && (!false || false) && !(p 141) && (!(p 141) || false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d4077, h141] at guard ⊢
theorem bound241 (p : Pattern) (guard : pushGuard support p 97 119 141 141 = true) : bonus 97 p ≤ 1 + Generated.soko2_2Potential.boulder 141 - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some 141)) := by
  have certified := compare1383 p (guard241 p guard)
  change d312 p ≤ (0 : Int) + d312 (change p 119 (some 141))
  have normalized := agree312 _ _ (change_representative support p 119 (some 141) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (0 : Int) + d312 (change p 10000 (some 141))
  rw [sub2415]
  exact certified
theorem check241 (p : Pattern) : (!pushGuard support p 97 119 141 141 || decide (bonus 97 p ≤ 1 + Generated.soko2_2Potential.boulder 141 - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some 141)))) = true :=
  check_of_implication _ _ (bound241 p)
theorem guard242 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 98 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound242 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 98 .east = true) : bonus 97 p ≤ bonus 98 p := by
  have certified := compare19 p (guard242 p guard)
  simpa only [at97, at98, Int.zero_add] using certified
theorem check242 (p : Pattern) : (!walkGuard soko2_2.board support p 97 98 .east || decide (bonus 97 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound242 p)
theorem guard243 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 96 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound243 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 96 .west = true) : bonus 97 p ≤ bonus 96 p := by
  have certified := compare19 p (guard243 p guard)
  simpa only [at97, at96, Int.zero_add] using certified
theorem check243 (p : Pattern) : (!walkGuard soko2_2.board support p 97 96 .west || decide (bonus 97 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound243 p)
theorem guard244 (p : Pattern) (guard : pushGuard support p 97 96 95 95 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound244 (p : Pattern) (guard : pushGuard support p 97 96 95 95 = true) : bonus 97 p ≤ 1 + Generated.soko2_2Potential.boulder 95 - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some 95)) := by
  have certified := compare20 p (guard244 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 96 (some 95))
  have normalized := agree312 _ _ (change_representative support p 96 (some 95) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check244 (p : Pattern) : (!pushGuard support p 97 96 95 95 || decide (bonus 97 p ≤ 1 + Generated.soko2_2Potential.boulder 95 - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some 95)))) = true :=
  check_of_implication _ _ (bound244 p)
theorem guard245 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 76 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound245 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 76 .northEast = true) : bonus 97 p ≤ bonus 76 p := by
  have certified := compare19 p (guard245 p guard)
  simpa only [at97, at76, Int.zero_add] using certified
theorem check245 (p : Pattern) : (!walkGuard soko2_2.board support p 97 76 .northEast || decide (bonus 97 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound245 p)
theorem guard246 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 74 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound246 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 74 .northWest = true) : bonus 97 p ≤ bonus 74 p := by
  have certified := compare19 p (guard246 p guard)
  simpa only [at97, at74, Int.zero_add] using certified
theorem check246 (p : Pattern) : (!walkGuard soko2_2.board support p 97 74 .northWest || decide (bonus 97 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound246 p)
theorem guard247 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 120 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound247 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 120 .southEast = true) : bonus 97 p ≤ bonus 120 p := by
  have certified := compare19 p (guard247 p guard)
  simpa only [at97, at120, Int.zero_add] using certified
theorem check247 (p : Pattern) : (!walkGuard soko2_2.board support p 97 120 .southEast || decide (bonus 97 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound247 p)
theorem guard248 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 118 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound248 (p : Pattern) (guard : walkGuard soko2_2.board support p 97 118 .southWest = true) : bonus 97 p ≤ bonus 118 p := by
  have certified := compare19 p (guard248 p guard)
  simpa only [at97, at118, Int.zero_add] using certified
theorem check248 (p : Pattern) : (!walkGuard soko2_2.board support p 97 118 .southWest || decide (bonus 97 p ≤ bonus 118 p)) = true :=
  check_of_implication _ _ (bound248 p)
theorem guard249 (p : Pattern) (guard : walkGuard soko2_2.board support p 98 76 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound249 (p : Pattern) (guard : walkGuard soko2_2.board support p 98 76 .north = true) : bonus 98 p ≤ bonus 76 p := by
  have certified := compare19 p (guard249 p guard)
  simpa only [at98, at76, Int.zero_add] using certified
theorem check249 (p : Pattern) : (!walkGuard soko2_2.board support p 98 76 .north || decide (bonus 98 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound249 p)
theorem guard250 (p : Pattern) (guard : walkGuard soko2_2.board support p 98 120 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound250 (p : Pattern) (guard : walkGuard soko2_2.board support p 98 120 .south = true) : bonus 98 p ≤ bonus 120 p := by
  have certified := compare19 p (guard250 p guard)
  simpa only [at98, at120, Int.zero_add] using certified
theorem check250 (p : Pattern) : (!walkGuard soko2_2.board support p 98 120 .south || decide (bonus 98 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound250 p)
theorem guard251 (p : Pattern) (guard : walkGuard soko2_2.board support p 98 97 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound251 (p : Pattern) (guard : walkGuard soko2_2.board support p 98 97 .west = true) : bonus 98 p ≤ bonus 97 p := by
  have certified := compare19 p (guard251 p guard)
  simpa only [at98, at97, Int.zero_add] using certified
theorem check251 (p : Pattern) : (!walkGuard soko2_2.board support p 98 97 .west || decide (bonus 98 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound251 p)
theorem guard252 (p : Pattern) (guard : pushGuard support p 98 97 96 96 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound252 (p : Pattern) (guard : pushGuard support p 98 97 96 96 = true) : bonus 98 p ≤ 1 + Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.boulder 97 + bonus 97 (change p 97 (some 96)) := by
  have certified := compare20 p (guard252 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 97 (some 96))
  have normalized := agree312 _ _ (change_representative support p 97 (some 96) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check252 (p : Pattern) : (!pushGuard support p 98 97 96 96 || decide (bonus 98 p ≤ 1 + Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.boulder 97 + bonus 97 (change p 97 (some 96)))) = true :=
  check_of_implication _ _ (bound252 p)
theorem guard253 (p : Pattern) (guard : walkGuard soko2_2.board support p 98 119 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound253 (p : Pattern) (guard : walkGuard soko2_2.board support p 98 119 .southWest = true) : bonus 98 p ≤ bonus 119 p := by
  have certified := compare19 p (guard253 p guard)
  simpa only [at98, at119, Int.zero_add] using certified
theorem check253 (p : Pattern) : (!walkGuard soko2_2.board support p 98 119 .southWest || decide (bonus 98 p ≤ bonus 119 p)) = true :=
  check_of_implication _ _ (bound253 p)
theorem guard254 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 78 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound254 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 78 .north = true) : bonus 100 p ≤ bonus 78 p := by
  have certified := compare1086 p (guard254 p guard)
  simpa only [at100, at78, Int.zero_add] using certified
theorem check254 (p : Pattern) : (!walkGuard soko2_2.board support p 100 78 .north || decide (bonus 100 p ≤ bonus 78 p)) = true :=
  check_of_implication _ _ (bound254 p)
theorem guard255 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 122 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound255 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 122 .south = true) : bonus 100 p ≤ bonus 122 p := by
  have certified := compare1086 p (guard255 p guard)
  simpa only [at100, at122, Int.zero_add] using certified
theorem check255 (p : Pattern) : (!walkGuard soko2_2.board support p 100 122 .south || decide (bonus 100 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound255 p)
theorem guard256 (p : Pattern) (guard : pushGuard support p 100 122 144 144 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound256 (p : Pattern) (guard : pushGuard support p 100 122 144 144 = true) : bonus 100 p ≤ 1 + Generated.soko2_2Potential.boulder 144 - Generated.soko2_2Potential.boulder 122 + bonus 122 (change p 122 (some 144)) := by
  have certified := compare1087 p (guard256 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 122 (some 144))
  have normalized := agree0 _ _ (change_representative support p 122 (some 144) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check256 (p : Pattern) : (!pushGuard support p 100 122 144 144 || decide (bonus 100 p ≤ 1 + Generated.soko2_2Potential.boulder 144 - Generated.soko2_2Potential.boulder 122 + bonus 122 (change p 122 (some 144)))) = true :=
  check_of_implication _ _ (bound256 p)
theorem guard257 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 101 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound257 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 101 .east = true) : bonus 100 p ≤ bonus 101 p := by
  have certified := compare1086 p (guard257 p guard)
  simpa only [at100, at101, Int.zero_add] using certified
theorem check257 (p : Pattern) : (!walkGuard soko2_2.board support p 100 101 .east || decide (bonus 100 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound257 p)
theorem guard258 (p : Pattern) (guard : pushGuard support p 100 101 102 102 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound258 (p : Pattern) (guard : pushGuard support p 100 101 102 102 = true) : bonus 100 p ≤ 1 + Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some 102)) := by
  have certified := compare1087 p (guard258 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 101 (some 102))
  have normalized := agree0 _ _ (change_representative support p 101 (some 102) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check258 (p : Pattern) : (!pushGuard support p 100 101 102 102 || decide (bonus 100 p ≤ 1 + Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some 102)))) = true :=
  check_of_implication _ _ (bound258 p)
theorem guard259 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 79 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound259 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 79 .northEast = true) : bonus 100 p ≤ bonus 79 p := by
  have certified := compare1086 p (guard259 p guard)
  simpa only [at100, at79, Int.zero_add] using certified
theorem check259 (p : Pattern) : (!walkGuard soko2_2.board support p 100 79 .northEast || decide (bonus 100 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound259 p)
theorem guard260 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 123 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound260 (p : Pattern) (guard : walkGuard soko2_2.board support p 100 123 .southEast = true) : bonus 100 p ≤ bonus 123 p := by
  have certified := compare1086 p (guard260 p guard)
  simpa only [at100, at123, Int.zero_add] using certified
theorem check260 (p : Pattern) : (!walkGuard soko2_2.board support p 100 123 .southEast || decide (bonus 100 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound260 p)
theorem guard261 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 79 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound261 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 79 .north = true) : bonus 101 p ≤ bonus 79 p := by
  have certified := compare1086 p (guard261 p guard)
  simpa only [at101, at79, Int.zero_add] using certified
theorem check261 (p : Pattern) : (!walkGuard soko2_2.board support p 101 79 .north || decide (bonus 101 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound261 p)
theorem guard262 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 123 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound262 (p : Pattern) (guard : walkGuard soko2_2.board support p 101 123 .south = true) : bonus 101 p ≤ bonus 123 p := by
  have certified := compare1086 p (guard262 p guard)
  simpa only [at101, at123, Int.zero_add] using certified
theorem check262 (p : Pattern) : (!walkGuard soko2_2.board support p 101 123 .south || decide (bonus 101 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound262 p)
theorem guard263 (p : Pattern) (guard : pushGuard support p 101 123 145 145 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound263 (p : Pattern) (guard : pushGuard support p 101 123 145 145 = true) : bonus 101 p ≤ 1 + Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some 145)) := by
  have certified := compare1087 p (guard263 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 123 (some 145))
  have normalized := agree0 _ _ (change_representative support p 123 (some 145) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check263 (p : Pattern) : (!pushGuard support p 101 123 145 145 || decide (bonus 101 p ≤ 1 + Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some 145)))) = true :=
  check_of_implication _ _ (bound263 p)
end NetHack.Sokoban22Refined85
