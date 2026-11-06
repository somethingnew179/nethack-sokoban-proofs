import NetHack.Sokoban12CostPartition.ActionBounds013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard336 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 167 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound336 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 167 .east = true) : bonus 166 p ≤ bonus 167 p := by
  have certified := compare897 p (guard336 p guard)
  simpa only [at166, at167, Int.zero_add] using certified
theorem check336 (p : Pattern) : (!walkGuard soko1_2.board support p 166 167 .east || decide (bonus 166 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound336 p)
theorem guard337 (p : Pattern) (guard : pushGuard support p 166 167 168 168 = true) : d770 p = 1 := by
  change (!false && (!false || false) && !(p 168) && (!(p 168) || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound337 (p : Pattern) (guard : pushGuard support p 166 167 168 168 = true) : bonus 166 p ≤ 1 + Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some 168)) := by
  have certified := compare2783 p (guard337 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 167 (some 168))
  have normalized := agree258 _ _ (change_representative support p 167 (some 168) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 (some 168))
  rw [sub1676]
  exact certified
theorem check337 (p : Pattern) : (!pushGuard support p 166 167 168 168 || decide (bonus 166 p ≤ 1 + Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some 168)))) = true :=
  check_of_implication _ _ (bound337 p)
theorem guard338 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 141 .northEast = true) : d768 p = 1 := by
  change (!false && !(p 141) && !(true && false && false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound338 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 141 .northEast = true) : bonus 166 p ≤ bonus 141 p := by
  have certified := compare1002 p (guard338 p guard)
  simpa only [at166, at141, Int.zero_add] using certified
theorem check338 (p : Pattern) : (!walkGuard soko1_2.board support p 166 141 .northEast || decide (bonus 166 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound338 p)
theorem guard339 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 193 .southEast = true) : d917 p = 1 := by
  change (!false && !(p 193) && !(true && (p 192) && false)) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, h192, h193] at guard ⊢
theorem bound339 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 193 .southEast = true) : bonus 166 p ≤ bonus 193 p := by
  have certified := compare2879 p (guard339 p guard)
  simpa only [at166, at193, Int.zero_add] using certified
theorem check339 (p : Pattern) : (!walkGuard soko1_2.board support p 166 193 .southEast || decide (bonus 166 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound339 p)
theorem guard340 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 191 .southWest = true) : d854 p = 1 := by
  change (!false && !false && !(true && (p 192) && true)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound340 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 191 .southWest = true) : bonus 166 p ≤ bonus 191 p := by
  have certified := compare2880 p (guard340 p guard)
  simpa only [at166, at191, Int.zero_add] using certified
theorem check340 (p : Pattern) : (!walkGuard soko1_2.board support p 166 191 .southWest || decide (bonus 166 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound340 p)
theorem guard341 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 141 .north = true) : d768 p = 1 := by
  change (!false && !(p 141) && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound341 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 141 .north = true) : bonus 167 p ≤ bonus 141 p := by
  have certified := compare1002 p (guard341 p guard)
  simpa only [at167, at141, Int.zero_add] using certified
theorem check341 (p : Pattern) : (!walkGuard soko1_2.board support p 167 141 .north || decide (bonus 167 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound341 p)
theorem guard342 (p : Pattern) (guard : pushGuard support p 167 141 115 115 = true) : d767 p = 1 := by
  change (!false && (!true || (p 141)) && !false && (!false || false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d767, h141] at guard ⊢
theorem bound342 (p : Pattern) (guard : pushGuard support p 167 141 115 115 = true) : bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder 115 - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some 115)) := by
  have certified := compare1071 p (guard342 p guard)
  change d258 p ≤ (1 : Int) + d309 (change p 141 (some 115))
  have normalized := agree309 _ _ (change_representative support p 141 (some 115) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d309 (change p 141 none)
  rw [sub268]
  exact certified
theorem check342 (p : Pattern) : (!pushGuard support p 167 141 115 115 || decide (bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder 115 - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some 115)))) = true :=
  check_of_implication _ _ (bound342 p)
theorem guard343 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 193 .south = true) : d917 p = 1 := by
  change (!false && !(p 193) && !false) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound343 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 193 .south = true) : bonus 167 p ≤ bonus 193 p := by
  have certified := compare2879 p (guard343 p guard)
  simpa only [at167, at193, Int.zero_add] using certified
theorem check343 (p : Pattern) : (!walkGuard soko1_2.board support p 167 193 .south || decide (bonus 167 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound343 p)
theorem guard344 (p : Pattern) (guard : pushGuard support p 167 193 219 219 = true) : d916 p = 1 := by
  change (!false && (!true || (p 193)) && !false && (!false || false)) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d916, h193] at guard ⊢
theorem bound344 (p : Pattern) (guard : pushGuard support p 167 193 219 219 = true) : bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder 219 - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some 219)) := by
  have certified := compare2953 p (guard344 p guard)
  change d258 p ≤ (2 : Int) + d658 (change p 193 (some 219))
  have normalized := agree658 _ _ (change_representative support p 193 (some 219) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d658 (change p 193 none)
  rw [sub1764]
  exact certified
theorem check344 (p : Pattern) : (!pushGuard support p 167 193 219 219 || decide (bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder 219 - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some 219)))) = true :=
  check_of_implication _ _ (bound344 p)
theorem guard345 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 168 .east = true) : d770 p = 1 := by
  change (!false && !(p 168) && !false) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound345 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 168 .east = true) : bonus 167 p ≤ bonus 168 p := by
  have certified := compare2997 p (guard345 p guard)
  simpa only [at167, at168, Int.zero_add] using certified
theorem check345 (p : Pattern) : (!walkGuard soko1_2.board support p 167 168 .east || decide (bonus 167 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound345 p)
theorem guard346 (p : Pattern) (guard : pushGuard support p 167 168 169 169 = true) : d769 p = 1 := by
  change (!false && (!true || (p 168)) && !false && (!false || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d769, h168] at guard ⊢
theorem bound346 (p : Pattern) (guard : pushGuard support p 167 168 169 169 = true) : bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder 169 - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some 169)) := by
  have certified := compare3048 p (guard346 p guard)
  change d258 p ≤ (1 : Int) + d430 (change p 168 (some 169))
  have normalized := agree430 _ _ (change_representative support p 168 (some 169) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d430 (change p 168 none)
  rw [sub1091]
  exact certified
theorem check346 (p : Pattern) : (!pushGuard support p 167 168 169 169 || decide (bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder 169 - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some 169)))) = true :=
  check_of_implication _ _ (bound346 p)
theorem guard347 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 166 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound347 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 166 .west = true) : bonus 167 p ≤ bonus 166 p := by
  have certified := compare897 p (guard347 p guard)
  simpa only [at167, at166, Int.zero_add] using certified
theorem check347 (p : Pattern) : (!walkGuard soko1_2.board support p 167 166 .west || decide (bonus 167 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound347 p)
theorem guard348 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 142 .northEast = true) : d986 p = 1 := by
  change (!false && !false && !(true && (p 141) && (p 168))) = true at guard
  cases h141 : p 141 <;> cases h168 : p 168
  all_goals simp [d0, d1, d770, d986, h141, h168] at guard ⊢
theorem bound348 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 142 .northEast = true) : bonus 167 p ≤ bonus 142 p := by
  have certified := compare3092 p (guard348 p guard)
  simpa only [at167, at142, Int.zero_add] using certified
theorem check348 (p : Pattern) : (!walkGuard soko1_2.board support p 167 142 .northEast || decide (bonus 167 p ≤ bonus 142 p)) = true :=
  check_of_implication _ _ (bound348 p)
theorem guard349 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 140 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 141) && false)) = true at guard
  cases h141 : p 141
  all_goals simp [d1, h141] at guard ⊢
theorem bound349 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 140 .northWest = true) : bonus 167 p ≤ bonus 140 p := by
  have certified := compare897 p (guard349 p guard)
  simpa only [at167, at140, Int.zero_add] using certified
theorem check349 (p : Pattern) : (!walkGuard soko1_2.board support p 167 140 .northWest || decide (bonus 167 p ≤ bonus 140 p)) = true :=
  check_of_implication _ _ (bound349 p)
theorem guard350 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 194 .southEast = true) : d1133 p = 1 := by
  change (!false && !false && !(true && (p 193) && (p 168))) = true at guard
  cases h168 : p 168 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d1133, h168, h193] at guard ⊢
theorem bound350 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 194 .southEast = true) : bonus 167 p ≤ bonus 194 p := by
  have certified := compare3093 p (guard350 p guard)
  simpa only [at167, at194, Int.zero_add] using certified
theorem check350 (p : Pattern) : (!walkGuard soko1_2.board support p 167 194 .southEast || decide (bonus 167 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound350 p)
theorem guard351 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 192 .southWest = true) : d854 p = 1 := by
  change (!false && !(p 192) && !(true && (p 193) && false)) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d854, h192, h193] at guard ⊢
theorem bound351 (p : Pattern) (guard : walkGuard soko1_2.board support p 167 192 .southWest = true) : bonus 167 p ≤ bonus 192 p := by
  have certified := compare2639 p (guard351 p guard)
  simpa only [at167, at192, Int.zero_add] using certified
theorem check351 (p : Pattern) : (!walkGuard soko1_2.board support p 167 192 .southWest || decide (bonus 167 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound351 p)
theorem guard352 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 142 .north = true) : d770 p = 1 := by
  change (!(p 168) && !false && !false) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound352 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 142 .north = true) : bonus 168 p ≤ bonus 142 p := by
  have certified := compare3161 p (guard352 p guard)
  simpa only [at168, at142, Int.zero_add] using certified
theorem check352 (p : Pattern) : (!walkGuard soko1_2.board support p 168 142 .north || decide (bonus 168 p ≤ bonus 142 p)) = true :=
  check_of_implication _ _ (bound352 p)
theorem guard353 (p : Pattern) (guard : pushGuard support p 168 142 116 116 = true) : d770 p = 1 := by
  change (!(p 168) && (!false || false) && !false && (!false || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound353 (p : Pattern) (guard : pushGuard support p 168 142 116 116 = true) : bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder 116 - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some 116)) := by
  have certified := compare3229 p (guard353 p guard)
  change d430 p ≤ (1 : Int) + d195 (change p 142 (some 116))
  have normalized := agree195 _ _ (change_representative support p 142 (some 116) 10000 dummy_outside)
  rw [normalized]
  change d430 p ≤ (1 : Int) + d195 (change p 10000 none)
  rw [sub285]
  exact certified
theorem check353 (p : Pattern) : (!pushGuard support p 168 142 116 116 || decide (bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder 116 - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some 116)))) = true :=
  check_of_implication _ _ (bound353 p)
theorem guard354 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 194 .south = true) : d770 p = 1 := by
  change (!(p 168) && !false && !false) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound354 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 194 .south = true) : bonus 168 p ≤ bonus 194 p := by
  have certified := compare3273 p (guard354 p guard)
  simpa only [at168, at194, Int.zero_add] using certified
theorem check354 (p : Pattern) : (!walkGuard soko1_2.board support p 168 194 .south || decide (bonus 168 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound354 p)
theorem guard355 (p : Pattern) (guard : pushGuard support p 168 194 220 220 = true) : d770 p = 1 := by
  change (!(p 168) && (!false || false) && !false && (!false || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound355 (p : Pattern) (guard : pushGuard support p 168 194 220 220 = true) : bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder 220 - Generated.soko1_2Potential.boulder 194 + bonus 194 (change p 194 (some 220)) := by
  have certified := compare3317 p (guard355 p guard)
  change d430 p ≤ (1 : Int) + d258 (change p 194 (some 220))
  have normalized := agree258 _ _ (change_representative support p 194 (some 220) 10000 dummy_outside)
  rw [normalized]
  change d430 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check355 (p : Pattern) : (!pushGuard support p 168 194 220 220 || decide (bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder 220 - Generated.soko1_2Potential.boulder 194 + bonus 194 (change p 194 (some 220)))) = true :=
  check_of_implication _ _ (bound355 p)
theorem guard356 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 169 .east = true) : d770 p = 1 := by
  change (!(p 168) && !false && !false) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound356 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 169 .east = true) : bonus 168 p ≤ bonus 169 p := by
  have certified := compare3161 p (guard356 p guard)
  simpa only [at168, at169, Int.zero_add] using certified
theorem check356 (p : Pattern) : (!walkGuard soko1_2.board support p 168 169 .east || decide (bonus 168 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound356 p)
theorem guard357 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 167 .west = true) : d770 p = 1 := by
  change (!(p 168) && !false && !false) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound357 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 167 .west = true) : bonus 168 p ≤ bonus 167 p := by
  have certified := compare3273 p (guard357 p guard)
  simpa only [at168, at167, Int.zero_add] using certified
theorem check357 (p : Pattern) : (!walkGuard soko1_2.board support p 168 167 .west || decide (bonus 168 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound357 p)
theorem guard358 (p : Pattern) (guard : pushGuard support p 168 167 166 166 = true) : d770 p = 1 := by
  change (!(p 168) && (!false || false) && !false && (!false || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound358 (p : Pattern) (guard : pushGuard support p 168 167 166 166 = true) : bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder 166 - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some 166)) := by
  have certified := compare3273 p (guard358 p guard)
  change d430 p ≤ (0 : Int) + d258 (change p 167 (some 166))
  have normalized := agree258 _ _ (change_representative support p 167 (some 166) 10000 dummy_outside)
  rw [normalized]
  change d430 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check358 (p : Pattern) : (!pushGuard support p 168 167 166 166 || decide (bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder 166 - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some 166)))) = true :=
  check_of_implication _ _ (bound358 p)
theorem guard359 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 143 .northEast = true) : d770 p = 1 := by
  change (!(p 168) && !false && !(true && false && false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound359 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 143 .northEast = true) : bonus 168 p ≤ bonus 143 p := by
  have certified := compare3161 p (guard359 p guard)
  simpa only [at168, at143, Int.zero_add] using certified
theorem check359 (p : Pattern) : (!walkGuard soko1_2.board support p 168 143 .northEast || decide (bonus 168 p ≤ bonus 143 p)) = true :=
  check_of_implication _ _ (bound359 p)
end NetHack.Sokoban12CostPartition
