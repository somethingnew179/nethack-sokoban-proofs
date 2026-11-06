import NetHack.Sokoban12CostPartition.ActionBounds009
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard240 (p : Pattern) (guard : walkGuard soko1_2.board support p 135 134 .west = true) : d737 p = 1 := by
  change (!false && !(p 134) && !false) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d737, h134] at guard ⊢
theorem bound240 (p : Pattern) (guard : walkGuard soko1_2.board support p 135 134 .west = true) : bonus 135 p ≤ bonus 134 p := by
  have certified := compare852 p (guard240 p guard)
  simpa only [at135, at134, Int.zero_add] using certified
theorem check240 (p : Pattern) : (!walkGuard soko1_2.board support p 135 134 .west || decide (bonus 135 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound240 p)
theorem guard241 (p : Pattern) (guard : pushGuard support p 135 134 133 133 = true) : d810 p = 1 := by
  change (!false && (!true || (p 134)) && !(p 133) && (!(p 133) || false)) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d736, d810, h133, h134] at guard ⊢
theorem bound241 (p : Pattern) (guard : pushGuard support p 135 134 133 133 = true) : bonus 135 p ≤ 1 + Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some 133)) := by
  have certified := compare881 p (guard241 p guard)
  change d236 p ≤ (2 : Int) + d74 (change p 134 (some 133))
  have normalized := agree74 _ _ (change_representative support p 134 (some 133) 10000 dummy_outside)
  rw [normalized]
  change d236 p ≤ (2 : Int) + d74 (change p 134 (some 133))
  rw [sub866]
  exact certified
theorem check241 (p : Pattern) : (!pushGuard support p 135 134 133 133 || decide (bonus 135 p ≤ 1 + Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some 133)))) = true :=
  check_of_implication _ _ (bound241 p)
theorem guard242 (p : Pattern) (guard : walkGuard soko1_2.board support p 135 108 .northWest = true) : d755 p = 1 := by
  change (!false && !(p 108) && !(true && true && (p 134))) = true at guard
  cases h108 : p 108 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d755, h108, h134] at guard ⊢
theorem bound242 (p : Pattern) (guard : walkGuard soko1_2.board support p 135 108 .northWest = true) : bonus 135 p ≤ bonus 108 p := by
  have certified := compare882 p (guard242 p guard)
  simpa only [at135, at108, Int.zero_add] using certified
theorem check242 (p : Pattern) : (!walkGuard soko1_2.board support p 135 108 .northWest || decide (bonus 135 p ≤ bonus 108 p)) = true :=
  check_of_implication _ _ (bound242 p)
theorem guard243 (p : Pattern) (guard : walkGuard soko1_2.board support p 135 160 .southWest = true) : d758 p = 1 := by
  change (!false && !(p 160) && !(true && false && (p 134))) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, h134, h160] at guard ⊢
theorem bound243 (p : Pattern) (guard : walkGuard soko1_2.board support p 135 160 .southWest = true) : bonus 135 p ≤ bonus 160 p := by
  have certified := compare896 p (guard243 p guard)
  simpa only [at135, at160, Int.zero_add] using certified
theorem check243 (p : Pattern) : (!walkGuard soko1_2.board support p 135 160 .southWest || decide (bonus 135 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound243 p)
theorem guard244 (p : Pattern) (guard : walkGuard soko1_2.board support p 140 166 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound244 (p : Pattern) (guard : walkGuard soko1_2.board support p 140 166 .south = true) : bonus 140 p ≤ bonus 166 p := by
  have certified := compare897 p (guard244 p guard)
  simpa only [at140, at166, Int.zero_add] using certified
theorem check244 (p : Pattern) : (!walkGuard soko1_2.board support p 140 166 .south || decide (bonus 140 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound244 p)
theorem guard245 (p : Pattern) (guard : pushGuard support p 140 166 192 192 = true) : d854 p = 1 := by
  change (!false && (!false || false) && !(p 192) && (!(p 192) || false)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound245 (p : Pattern) (guard : pushGuard support p 140 166 192 192 = true) : bonus 140 p ≤ 1 + Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.boulder 166 + bonus 166 (change p 166 (some 192)) := by
  have certified := compare974 p (guard245 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 166 (some 192))
  have normalized := agree258 _ _ (change_representative support p 166 (some 192) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 (some 192))
  rw [sub944]
  exact certified
theorem check245 (p : Pattern) : (!pushGuard support p 140 166 192 192 || decide (bonus 140 p ≤ 1 + Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.boulder 166 + bonus 166 (change p 166 (some 192)))) = true :=
  check_of_implication _ _ (bound245 p)
theorem guard246 (p : Pattern) (guard : walkGuard soko1_2.board support p 140 141 .east = true) : d768 p = 1 := by
  change (!false && !(p 141) && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound246 (p : Pattern) (guard : walkGuard soko1_2.board support p 140 141 .east = true) : bonus 140 p ≤ bonus 141 p := by
  have certified := compare1002 p (guard246 p guard)
  simpa only [at140, at141, Int.zero_add] using certified
theorem check246 (p : Pattern) : (!walkGuard soko1_2.board support p 140 141 .east || decide (bonus 140 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound246 p)
theorem guard247 (p : Pattern) (guard : pushGuard support p 140 141 142 142 = true) : d767 p = 1 := by
  change (!false && (!true || (p 141)) && !false && (!false || false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d767, h141] at guard ⊢
theorem bound247 (p : Pattern) (guard : pushGuard support p 140 141 142 142 = true) : bonus 140 p ≤ 1 + Generated.soko1_2Potential.boulder 142 - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some 142)) := by
  have certified := compare1071 p (guard247 p guard)
  change d258 p ≤ (1 : Int) + d309 (change p 141 (some 142))
  have normalized := agree309 _ _ (change_representative support p 141 (some 142) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d309 (change p 141 none)
  rw [sub268]
  exact certified
theorem check247 (p : Pattern) : (!pushGuard support p 140 141 142 142 || decide (bonus 140 p ≤ 1 + Generated.soko1_2Potential.boulder 142 - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some 142)))) = true :=
  check_of_implication _ _ (bound247 p)
theorem guard248 (p : Pattern) (guard : walkGuard soko1_2.board support p 140 115 .northEast = true) : d768 p = 1 := by
  change (!false && !false && !(true && true && (p 141))) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound248 (p : Pattern) (guard : walkGuard soko1_2.board support p 140 115 .northEast = true) : bonus 140 p ≤ bonus 115 p := by
  have certified := compare1099 p (guard248 p guard)
  simpa only [at140, at115, Int.zero_add] using certified
theorem check248 (p : Pattern) : (!walkGuard soko1_2.board support p 140 115 .northEast || decide (bonus 140 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound248 p)
theorem guard249 (p : Pattern) (guard : walkGuard soko1_2.board support p 140 167 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 141))) = true at guard
  cases h141 : p 141
  all_goals simp [d1, h141] at guard ⊢
theorem bound249 (p : Pattern) (guard : walkGuard soko1_2.board support p 140 167 .southEast = true) : bonus 140 p ≤ bonus 167 p := by
  have certified := compare897 p (guard249 p guard)
  simpa only [at140, at167, Int.zero_add] using certified
theorem check249 (p : Pattern) : (!walkGuard soko1_2.board support p 140 167 .southEast || decide (bonus 140 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound249 p)
theorem guard250 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 115 .north = true) : d768 p = 1 := by
  change (!(p 141) && !false && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound250 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 115 .north = true) : bonus 141 p ≤ bonus 115 p := by
  have certified := compare1127 p (guard250 p guard)
  simpa only [at141, at115, Int.zero_add] using certified
theorem check250 (p : Pattern) : (!walkGuard soko1_2.board support p 141 115 .north || decide (bonus 141 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound250 p)
theorem guard251 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 167 .south = true) : d768 p = 1 := by
  change (!(p 141) && !false && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound251 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 167 .south = true) : bonus 141 p ≤ bonus 167 p := by
  have certified := compare1155 p (guard251 p guard)
  simpa only [at141, at167, Int.zero_add] using certified
theorem check251 (p : Pattern) : (!walkGuard soko1_2.board support p 141 167 .south || decide (bonus 141 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound251 p)
theorem guard252 (p : Pattern) (guard : pushGuard support p 141 167 193 193 = true) : d918 p = 1 := by
  change (!(p 141) && (!false || false) && !(p 193) && (!(p 193) || false)) = true at guard
  cases h141 : p 141 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d918, h141, h193] at guard ⊢
theorem bound252 (p : Pattern) (guard : pushGuard support p 141 167 193 193 = true) : bonus 141 p ≤ 1 + Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some 193)) := by
  have certified := compare1209 p (guard252 p guard)
  change d309 p ≤ (0 : Int) + d258 (change p 167 (some 193))
  have normalized := agree258 _ _ (change_representative support p 167 (some 193) 10000 dummy_outside)
  rw [normalized]
  change d309 p ≤ (0 : Int) + d258 (change p 10000 (some 193))
  rw [sub1022]
  exact certified
theorem check252 (p : Pattern) : (!pushGuard support p 141 167 193 193 || decide (bonus 141 p ≤ 1 + Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some 193)))) = true :=
  check_of_implication _ _ (bound252 p)
theorem guard253 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 142 .east = true) : d768 p = 1 := by
  change (!(p 141) && !false && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound253 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 142 .east = true) : bonus 141 p ≤ bonus 142 p := by
  have certified := compare1127 p (guard253 p guard)
  simpa only [at141, at142, Int.zero_add] using certified
theorem check253 (p : Pattern) : (!walkGuard soko1_2.board support p 141 142 .east || decide (bonus 141 p ≤ bonus 142 p)) = true :=
  check_of_implication _ _ (bound253 p)
theorem guard254 (p : Pattern) (guard : pushGuard support p 141 142 143 143 = true) : d768 p = 1 := by
  change (!(p 141) && (!false || false) && !false && (!false || false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound254 (p : Pattern) (guard : pushGuard support p 141 142 143 143 = true) : bonus 141 p ≤ 1 + Generated.soko1_2Potential.boulder 143 - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some 143)) := by
  have certified := compare1244 p (guard254 p guard)
  change d309 p ≤ (1 : Int) + d195 (change p 142 (some 143))
  have normalized := agree195 _ _ (change_representative support p 142 (some 143) 10000 dummy_outside)
  rw [normalized]
  change d309 p ≤ (1 : Int) + d195 (change p 10000 none)
  rw [sub285]
  exact certified
theorem check254 (p : Pattern) : (!pushGuard support p 141 142 143 143 || decide (bonus 141 p ≤ 1 + Generated.soko1_2Potential.boulder 143 - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some 143)))) = true :=
  check_of_implication _ _ (bound254 p)
theorem guard255 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 140 .west = true) : d768 p = 1 := by
  change (!(p 141) && !false && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound255 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 140 .west = true) : bonus 141 p ≤ bonus 140 p := by
  have certified := compare1155 p (guard255 p guard)
  simpa only [at141, at140, Int.zero_add] using certified
theorem check255 (p : Pattern) : (!walkGuard soko1_2.board support p 141 140 .west || decide (bonus 141 p ≤ bonus 140 p)) = true :=
  check_of_implication _ _ (bound255 p)
theorem guard256 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 116 .northEast = true) : d768 p = 1 := by
  change (!(p 141) && !false && !(true && false && false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound256 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 116 .northEast = true) : bonus 141 p ≤ bonus 116 p := by
  have certified := compare1127 p (guard256 p guard)
  simpa only [at141, at116, Int.zero_add] using certified
theorem check256 (p : Pattern) : (!walkGuard soko1_2.board support p 141 116 .northEast || decide (bonus 141 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound256 p)
theorem guard257 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 168 .southEast = true) : d984 p = 1 := by
  change (!(p 141) && !(p 168) && !(true && false && false)) = true at guard
  cases h141 : p 141 <;> cases h168 : p 168
  all_goals simp [d0, d1, d770, d984, h141, h168] at guard ⊢
theorem bound257 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 168 .southEast = true) : bonus 141 p ≤ bonus 168 p := by
  have certified := compare1299 p (guard257 p guard)
  simpa only [at141, at168, Int.zero_add] using certified
theorem check257 (p : Pattern) : (!walkGuard soko1_2.board support p 141 168 .southEast || decide (bonus 141 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound257 p)
theorem guard258 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 166 .southWest = true) : d768 p = 1 := by
  change (!(p 141) && !false && !(true && false && false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound258 (p : Pattern) (guard : walkGuard soko1_2.board support p 141 166 .southWest = true) : bonus 141 p ≤ bonus 166 p := by
  have certified := compare1155 p (guard258 p guard)
  simpa only [at141, at166, Int.zero_add] using certified
theorem check258 (p : Pattern) : (!walkGuard soko1_2.board support p 141 166 .southWest || decide (bonus 141 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound258 p)
theorem guard259 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 116 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound259 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 116 .north = true) : bonus 142 p ≤ bonus 116 p := by
  have certified := compare245 p (guard259 p guard)
  simpa only [at142, at116, Int.zero_add] using certified
theorem check259 (p : Pattern) : (!walkGuard soko1_2.board support p 142 116 .north || decide (bonus 142 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound259 p)
theorem guard260 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 168 .south = true) : d770 p = 1 := by
  change (!false && !(p 168) && !false) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound260 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 168 .south = true) : bonus 142 p ≤ bonus 168 p := by
  have certified := compare1343 p (guard260 p guard)
  simpa only [at142, at168, Int.zero_add] using certified
theorem check260 (p : Pattern) : (!walkGuard soko1_2.board support p 142 168 .south || decide (bonus 142 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound260 p)
theorem guard261 (p : Pattern) (guard : pushGuard support p 142 168 194 194 = true) : d769 p = 1 := by
  change (!false && (!true || (p 168)) && !false && (!false || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d769, h168] at guard ⊢
theorem bound261 (p : Pattern) (guard : pushGuard support p 142 168 194 194 = true) : bonus 142 p ≤ 1 + Generated.soko1_2Potential.boulder 194 - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some 194)) := by
  have certified := compare1344 p (guard261 p guard)
  change d195 p ≤ (1 : Int) + d430 (change p 168 (some 194))
  have normalized := agree430 _ _ (change_representative support p 168 (some 194) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (1 : Int) + d430 (change p 168 none)
  rw [sub1091]
  exact certified
theorem check261 (p : Pattern) : (!pushGuard support p 142 168 194 194 || decide (bonus 142 p ≤ 1 + Generated.soko1_2Potential.boulder 194 - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some 194)))) = true :=
  check_of_implication _ _ (bound261 p)
theorem guard262 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 143 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound262 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 143 .east = true) : bonus 142 p ≤ bonus 143 p := by
  have certified := compare245 p (guard262 p guard)
  simpa only [at142, at143, Int.zero_add] using certified
theorem check262 (p : Pattern) : (!walkGuard soko1_2.board support p 142 143 .east || decide (bonus 142 p ≤ bonus 143 p)) = true :=
  check_of_implication _ _ (bound262 p)
theorem guard263 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 141 .west = true) : d768 p = 1 := by
  change (!false && !(p 141) && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound263 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 141 .west = true) : bonus 142 p ≤ bonus 141 p := by
  have certified := compare243 p (guard263 p guard)
  simpa only [at142, at141, Int.zero_add] using certified
theorem check263 (p : Pattern) : (!walkGuard soko1_2.board support p 142 141 .west || decide (bonus 142 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound263 p)
end NetHack.Sokoban12CostPartition
