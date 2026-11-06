import NetHack.Sokoban12CostPartition.ActionBounds016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard408 (p : Pattern) (guard : pushGuard support p 187 186 185 185 = true) : d1158 p = 1 := by
  change (!(p 187) && (!true || (p 186)) && !false && (!false || false)) = true at guard
  cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d851, d1158, h186, h187] at guard ⊢
theorem bound408 (p : Pattern) (guard : pushGuard support p 187 186 185 185 = true) : bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some 185)) := by
  have certified := compare4416 p (guard408 p guard)
  change d524 p ≤ (2 : Int) + d485 (change p 186 (some 185))
  have normalized := agree485 _ _ (change_representative support p 186 (some 185) 10000 dummy_outside)
  rw [normalized]
  change d524 p ≤ (2 : Int) + d485 (change p 186 none)
  rw [sub1415]
  exact certified
theorem check408 (p : Pattern) : (!pushGuard support p 187 186 185 185 || decide (bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some 185)))) = true :=
  check_of_implication _ _ (bound408 p)
theorem guard409 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 160 .northWest = true) : d1047 p = 1 := by
  change (!(p 187) && !(p 160) && !(true && false && (p 186))) = true at guard
  cases h160 : p 160 <;> cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d851, d1047, h160, h186, h187] at guard ⊢
theorem bound409 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 160 .northWest = true) : bonus 187 p ≤ bonus 160 p := by
  have certified := compare4439 p (guard409 p guard)
  simpa only [at187, at160, Int.zero_add] using certified
theorem check409 (p : Pattern) : (!walkGuard soko1_2.board support p 187 160 .northWest || decide (bonus 187 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound409 p)
theorem guard410 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 214 .southEast = true) : d851 p = 1 := by
  change (!(p 187) && !false && !(true && false && true)) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound410 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 214 .southEast = true) : bonus 187 p ≤ bonus 214 p := by
  have certified := compare4255 p (guard410 p guard)
  simpa only [at187, at214, Int.zero_add] using certified
theorem check410 (p : Pattern) : (!walkGuard soko1_2.board support p 187 214 .southEast || decide (bonus 187 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound410 p)
theorem guard411 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 212 .southWest = true) : d851 p = 1 := by
  change (!(p 187) && !false && !(true && false && (p 186))) = true at guard
  cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d851, h186, h187] at guard ⊢
theorem bound411 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 212 .southWest = true) : bonus 187 p ≤ bonus 212 p := by
  have certified := compare4255 p (guard411 p guard)
  simpa only [at187, at212, Int.zero_add] using certified
theorem check411 (p : Pattern) : (!walkGuard soko1_2.board support p 187 212 .southWest || decide (bonus 187 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound411 p)
theorem guard412 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 163 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound412 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 163 .north = true) : bonus 189 p ≤ bonus 163 p := by
  have certified := compare897 p (guard412 p guard)
  simpa only [at189, at163, Int.zero_add] using certified
theorem check412 (p : Pattern) : (!walkGuard soko1_2.board support p 189 163 .north || decide (bonus 189 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound412 p)
theorem guard413 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 215 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound413 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 215 .south = true) : bonus 189 p ≤ bonus 215 p := by
  have certified := compare897 p (guard413 p guard)
  simpa only [at189, at215, Int.zero_add] using certified
theorem check413 (p : Pattern) : (!walkGuard soko1_2.board support p 189 215 .south || decide (bonus 189 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound413 p)
theorem guard414 (p : Pattern) (guard : pushGuard support p 189 215 241 241 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound414 (p : Pattern) (guard : pushGuard support p 189 215 241 241 = true) : bonus 189 p ≤ 1 + Generated.soko1_2Potential.boulder 241 - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some 241)) := by
  have certified := compare4440 p (guard414 p guard)
  change d258 p ≤ (8 : Int) + d258 (change p 215 (some 241))
  have normalized := agree258 _ _ (change_representative support p 215 (some 241) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (8 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check414 (p : Pattern) : (!pushGuard support p 189 215 241 241 || decide (bonus 189 p ≤ 1 + Generated.soko1_2Potential.boulder 241 - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some 241)))) = true :=
  check_of_implication _ _ (bound414 p)
theorem guard415 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 190 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound415 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 190 .east = true) : bonus 189 p ≤ bonus 190 p := by
  have certified := compare897 p (guard415 p guard)
  simpa only [at189, at190, Int.zero_add] using certified
theorem check415 (p : Pattern) : (!walkGuard soko1_2.board support p 189 190 .east || decide (bonus 189 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound415 p)
theorem guard416 (p : Pattern) (guard : pushGuard support p 189 190 191 191 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound416 (p : Pattern) (guard : pushGuard support p 189 190 191 191 = true) : bonus 189 p ≤ 1 + Generated.soko1_2Potential.boulder 191 - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some 191)) := by
  have certified := compare2570 p (guard416 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 190 (some 191))
  have normalized := agree258 _ _ (change_representative support p 190 (some 191) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check416 (p : Pattern) : (!pushGuard support p 189 190 191 191 || decide (bonus 189 p ≤ 1 + Generated.soko1_2Potential.boulder 191 - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some 191)))) = true :=
  check_of_implication _ _ (bound416 p)
theorem guard417 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 164 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound417 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 164 .northEast = true) : bonus 189 p ≤ bonus 164 p := by
  have certified := compare897 p (guard417 p guard)
  simpa only [at189, at164, Int.zero_add] using certified
theorem check417 (p : Pattern) : (!walkGuard soko1_2.board support p 189 164 .northEast || decide (bonus 189 p ≤ bonus 164 p)) = true :=
  check_of_implication _ _ (bound417 p)
theorem guard418 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 216 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound418 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 216 .southEast = true) : bonus 189 p ≤ bonus 216 p := by
  have certified := compare897 p (guard418 p guard)
  simpa only [at189, at216, Int.zero_add] using certified
theorem check418 (p : Pattern) : (!walkGuard soko1_2.board support p 189 216 .southEast || decide (bonus 189 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound418 p)
theorem guard419 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 214 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound419 (p : Pattern) (guard : walkGuard soko1_2.board support p 189 214 .southWest = true) : bonus 189 p ≤ bonus 214 p := by
  have certified := compare897 p (guard419 p guard)
  simpa only [at189, at214, Int.zero_add] using certified
theorem check419 (p : Pattern) : (!walkGuard soko1_2.board support p 189 214 .southWest || decide (bonus 189 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound419 p)
theorem guard420 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 164 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound420 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 164 .north = true) : bonus 190 p ≤ bonus 164 p := by
  have certified := compare897 p (guard420 p guard)
  simpa only [at190, at164, Int.zero_add] using certified
theorem check420 (p : Pattern) : (!walkGuard soko1_2.board support p 190 164 .north || decide (bonus 190 p ≤ bonus 164 p)) = true :=
  check_of_implication _ _ (bound420 p)
theorem guard421 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 216 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound421 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 216 .south = true) : bonus 190 p ≤ bonus 216 p := by
  have certified := compare897 p (guard421 p guard)
  simpa only [at190, at216, Int.zero_add] using certified
theorem check421 (p : Pattern) : (!walkGuard soko1_2.board support p 190 216 .south || decide (bonus 190 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound421 p)
theorem guard422 (p : Pattern) (guard : pushGuard support p 190 216 242 242 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound422 (p : Pattern) (guard : pushGuard support p 190 216 242 242 = true) : bonus 190 p ≤ 1 + Generated.soko1_2Potential.boulder 242 - Generated.soko1_2Potential.boulder 216 + bonus 216 (change p 216 (some 242)) := by
  have certified := compare4441 p (guard422 p guard)
  change d258 p ≤ (5 : Int) + d258 (change p 216 (some 242))
  have normalized := agree258 _ _ (change_representative support p 216 (some 242) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (5 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check422 (p : Pattern) : (!pushGuard support p 190 216 242 242 || decide (bonus 190 p ≤ 1 + Generated.soko1_2Potential.boulder 242 - Generated.soko1_2Potential.boulder 216 + bonus 216 (change p 216 (some 242)))) = true :=
  check_of_implication _ _ (bound422 p)
theorem guard423 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 191 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound423 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 191 .east = true) : bonus 190 p ≤ bonus 191 p := by
  have certified := compare897 p (guard423 p guard)
  simpa only [at190, at191, Int.zero_add] using certified
theorem check423 (p : Pattern) : (!walkGuard soko1_2.board support p 190 191 .east || decide (bonus 190 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound423 p)
theorem guard424 (p : Pattern) (guard : pushGuard support p 190 191 192 192 = true) : d854 p = 1 := by
  change (!false && (!false || false) && !(p 192) && (!(p 192) || false)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound424 (p : Pattern) (guard : pushGuard support p 190 191 192 192 = true) : bonus 190 p ≤ 1 + Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.boulder 191 + bonus 191 (change p 191 (some 192)) := by
  have certified := compare4514 p (guard424 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 191 (some 192))
  have normalized := agree258 _ _ (change_representative support p 191 (some 192) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 (some 192))
  rw [sub944]
  exact certified
theorem check424 (p : Pattern) : (!pushGuard support p 190 191 192 192 || decide (bonus 190 p ≤ 1 + Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.boulder 191 + bonus 191 (change p 191 (some 192)))) = true :=
  check_of_implication _ _ (bound424 p)
theorem guard425 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 189 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound425 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 189 .west = true) : bonus 190 p ≤ bonus 189 p := by
  have certified := compare897 p (guard425 p guard)
  simpa only [at190, at189, Int.zero_add] using certified
theorem check425 (p : Pattern) : (!walkGuard soko1_2.board support p 190 189 .west || decide (bonus 190 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound425 p)
theorem guard426 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 163 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound426 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 163 .northWest = true) : bonus 190 p ≤ bonus 163 p := by
  have certified := compare897 p (guard426 p guard)
  simpa only [at190, at163, Int.zero_add] using certified
theorem check426 (p : Pattern) : (!walkGuard soko1_2.board support p 190 163 .northWest || decide (bonus 190 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound426 p)
theorem guard427 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 215 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound427 (p : Pattern) (guard : walkGuard soko1_2.board support p 190 215 .southWest = true) : bonus 190 p ≤ bonus 215 p := by
  have certified := compare897 p (guard427 p guard)
  simpa only [at190, at215, Int.zero_add] using certified
theorem check427 (p : Pattern) : (!walkGuard soko1_2.board support p 190 215 .southWest || decide (bonus 190 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound427 p)
theorem guard428 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 192 .east = true) : d854 p = 1 := by
  change (!false && !(p 192) && !false) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound428 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 192 .east = true) : bonus 191 p ≤ bonus 192 p := by
  have certified := compare2639 p (guard428 p guard)
  simpa only [at191, at192, Int.zero_add] using certified
theorem check428 (p : Pattern) : (!walkGuard soko1_2.board support p 191 192 .east || decide (bonus 191 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound428 p)
theorem guard429 (p : Pattern) (guard : pushGuard support p 191 192 193 193 = true) : d1174 p = 1 := by
  change (!false && (!true || (p 192)) && !(p 193) && (!(p 193) || false)) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d1174, h192, h193] at guard ⊢
theorem bound429 (p : Pattern) (guard : pushGuard support p 191 192 193 193 = true) : bonus 191 p ≤ 1 + Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some 193)) := by
  have certified := compare4587 p (guard429 p guard)
  change d258 p ≤ (2 : Int) + d586 (change p 192 (some 193))
  have normalized := agree586 _ _ (change_representative support p 192 (some 193) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d586 (change p 192 (some 193))
  rw [sub2137]
  exact certified
theorem check429 (p : Pattern) : (!pushGuard support p 191 192 193 193 || decide (bonus 191 p ≤ 1 + Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some 193)))) = true :=
  check_of_implication _ _ (bound429 p)
theorem guard430 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 190 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound430 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 190 .west = true) : bonus 191 p ≤ bonus 190 p := by
  have certified := compare897 p (guard430 p guard)
  simpa only [at191, at190, Int.zero_add] using certified
theorem check430 (p : Pattern) : (!walkGuard soko1_2.board support p 191 190 .west || decide (bonus 191 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound430 p)
theorem guard431 (p : Pattern) (guard : pushGuard support p 191 190 189 189 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound431 (p : Pattern) (guard : pushGuard support p 191 190 189 189 = true) : bonus 191 p ≤ 1 + Generated.soko1_2Potential.boulder 189 - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some 189)) := by
  have certified := compare897 p (guard431 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 190 (some 189))
  have normalized := agree258 _ _ (change_representative support p 190 (some 189) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check431 (p : Pattern) : (!pushGuard support p 191 190 189 189 || decide (bonus 191 p ≤ 1 + Generated.soko1_2Potential.boulder 189 - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some 189)))) = true :=
  check_of_implication _ _ (bound431 p)
end NetHack.Sokoban12CostPartition
