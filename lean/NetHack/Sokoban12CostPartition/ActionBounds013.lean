import NetHack.Sokoban12CostPartition.ActionBounds012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard312 (p : Pattern) (guard : pushGuard support p 160 159 158 158 = true) : d1001 p = 1 := by
  change (!(p 160) && (!true || (p 159)) && !(p 158) && (!(p 158) || false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d1000, d1001, h158, h159, h160] at guard ⊢
theorem bound312 (p : Pattern) (guard : pushGuard support p 160 159 158 158 = true) : bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some 158)) := by
  have certified := compare2352 p (guard312 p guard)
  change d374 p ≤ (2 : Int) + d356 (change p 159 (some 158))
  have normalized := agree356 _ _ (change_representative support p 159 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d374 p ≤ (2 : Int) + d356 (change p 159 (some 158))
  rw [sub1469]
  exact certified
theorem check312 (p : Pattern) : (!pushGuard support p 160 159 158 158 || decide (bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some 158)))) = true :=
  check_of_implication _ _ (bound312 p)
theorem guard313 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 135 .northEast = true) : d758 p = 1 := by
  change (!(p 160) && !false && !(true && (p 134) && false)) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, h134, h160] at guard ⊢
theorem bound313 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 135 .northEast = true) : bonus 160 p ≤ bonus 135 p := by
  have certified := compare2289 p (guard313 p guard)
  simpa only [at160, at135, Int.zero_add] using certified
theorem check313 (p : Pattern) : (!walkGuard soko1_2.board support p 160 135 .northEast || decide (bonus 160 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound313 p)
theorem guard314 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 133 .northWest = true) : d820 p = 1 := by
  change (!(p 160) && !(p 133) && !(true && (p 134) && (p 159))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d818, d819, d820, h133, h134, h159, h160] at guard ⊢
theorem bound314 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 133 .northWest = true) : bonus 160 p ≤ bonus 133 p := by
  have certified := compare2367 p (guard314 p guard)
  simpa only [at160, at133, Int.zero_add] using certified
theorem check314 (p : Pattern) : (!walkGuard soko1_2.board support p 160 133 .northWest || decide (bonus 160 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound314 p)
theorem guard315 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 187 .southEast = true) : d1047 p = 1 := by
  change (!(p 160) && !(p 187) && !(true && (p 186) && false)) = true at guard
  cases h160 : p 160 <;> cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d851, d1047, h160, h186, h187] at guard ⊢
theorem bound315 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 187 .southEast = true) : bonus 160 p ≤ bonus 187 p := by
  have certified := compare2396 p (guard315 p guard)
  simpa only [at160, at187, Int.zero_add] using certified
theorem check315 (p : Pattern) : (!walkGuard soko1_2.board support p 160 187 .southEast || decide (bonus 160 p ≤ bonus 187 p)) = true :=
  check_of_implication _ _ (bound315 p)
theorem guard316 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 185 .southWest = true) : d1050 p = 1 := by
  change (!(p 160) && !false && !(true && (p 186) && (p 159))) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d758, d829, d1016, d1050, h159, h160, h186] at guard ⊢
theorem bound316 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 185 .southWest = true) : bonus 160 p ≤ bonus 185 p := by
  have certified := compare2453 p (guard316 p guard)
  simpa only [at160, at185, Int.zero_add] using certified
theorem check316 (p : Pattern) : (!walkGuard soko1_2.board support p 160 185 .southWest || decide (bonus 160 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound316 p)
theorem guard317 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 135 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound317 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 135 .north = true) : bonus 161 p ≤ bonus 135 p := by
  have certified := compare843 p (guard317 p guard)
  simpa only [at161, at135, Int.zero_add] using certified
theorem check317 (p : Pattern) : (!walkGuard soko1_2.board support p 161 135 .north || decide (bonus 161 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound317 p)
theorem guard318 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 187 .south = true) : d851 p = 1 := by
  change (!false && !(p 187) && !false) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound318 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 187 .south = true) : bonus 161 p ≤ bonus 187 p := by
  have certified := compare2483 p (guard318 p guard)
  simpa only [at161, at187, Int.zero_add] using certified
theorem check318 (p : Pattern) : (!walkGuard soko1_2.board support p 161 187 .south || decide (bonus 161 p ≤ bonus 187 p)) = true :=
  check_of_implication _ _ (bound318 p)
theorem guard319 (p : Pattern) (guard : pushGuard support p 161 187 213 213 = true) : d850 p = 1 := by
  change (!false && (!true || (p 187)) && !false && (!false || false)) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d850, h187] at guard ⊢
theorem bound319 (p : Pattern) (guard : pushGuard support p 161 187 213 213 = true) : bonus 161 p ≤ 1 + Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.boulder 187 + bonus 187 (change p 187 (some 213)) := by
  have certified := compare2484 p (guard319 p guard)
  change d236 p ≤ (0 : Int) + d524 (change p 187 (some 213))
  have normalized := agree524 _ _ (change_representative support p 187 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d236 p ≤ (0 : Int) + d524 (change p 187 none)
  rw [sub1517]
  exact certified
theorem check319 (p : Pattern) : (!pushGuard support p 161 187 213 213 || decide (bonus 161 p ≤ 1 + Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.boulder 187 + bonus 187 (change p 187 (some 213)))) = true :=
  check_of_implication _ _ (bound319 p)
theorem guard320 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 160 .west = true) : d758 p = 1 := by
  change (!false && !(p 160) && !false) = true at guard
  cases h160 : p 160
  all_goals simp [d0, d1, d758, h160] at guard ⊢
theorem bound320 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 160 .west = true) : bonus 161 p ≤ bonus 160 p := by
  have certified := compare896 p (guard320 p guard)
  simpa only [at161, at160, Int.zero_add] using certified
theorem check320 (p : Pattern) : (!walkGuard soko1_2.board support p 161 160 .west || decide (bonus 161 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound320 p)
theorem guard321 (p : Pattern) (guard : pushGuard support p 161 160 159 159 = true) : d1014 p = 1 := by
  change (!false && (!true || (p 160)) && !(p 159) && (!(p 159) || false)) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d757, d1014, h159, h160] at guard ⊢
theorem bound321 (p : Pattern) (guard : pushGuard support p 161 160 159 159 = true) : bonus 161 p ≤ 1 + Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some 159)) := by
  have certified := compare2521 p (guard321 p guard)
  change d236 p ≤ (2 : Int) + d374 (change p 160 (some 159))
  have normalized := agree374 _ _ (change_representative support p 160 (some 159) 10000 dummy_outside)
  rw [normalized]
  change d236 p ≤ (2 : Int) + d374 (change p 160 (some 159))
  rw [sub1552]
  exact certified
theorem check321 (p : Pattern) : (!pushGuard support p 161 160 159 159 || decide (bonus 161 p ≤ 1 + Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some 159)))) = true :=
  check_of_implication _ _ (bound321 p)
theorem guard322 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 134 .northWest = true) : d737 p = 1 := by
  change (!false && !(p 134) && !(true && false && (p 160))) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d737, h134, h160] at guard ⊢
theorem bound322 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 134 .northWest = true) : bonus 161 p ≤ bonus 134 p := by
  have certified := compare852 p (guard322 p guard)
  simpa only [at161, at134, Int.zero_add] using certified
theorem check322 (p : Pattern) : (!walkGuard soko1_2.board support p 161 134 .northWest || decide (bonus 161 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound322 p)
theorem guard323 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 186 .southWest = true) : d1054 p = 1 := by
  change (!false && !(p 186) && !(true && (p 187) && (p 160))) = true at guard
  cases h160 : p 160 <;> cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d829, d851, d1053, d1054, h160, h186, h187] at guard ⊢
theorem bound323 (p : Pattern) (guard : walkGuard soko1_2.board support p 161 186 .southWest = true) : bonus 161 p ≤ bonus 186 p := by
  have certified := compare2569 p (guard323 p guard)
  simpa only [at161, at186, Int.zero_add] using certified
theorem check323 (p : Pattern) : (!walkGuard soko1_2.board support p 161 186 .southWest || decide (bonus 161 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound323 p)
theorem guard324 (p : Pattern) (guard : walkGuard soko1_2.board support p 163 189 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound324 (p : Pattern) (guard : walkGuard soko1_2.board support p 163 189 .south = true) : bonus 163 p ≤ bonus 189 p := by
  have certified := compare897 p (guard324 p guard)
  simpa only [at163, at189, Int.zero_add] using certified
theorem check324 (p : Pattern) : (!walkGuard soko1_2.board support p 163 189 .south || decide (bonus 163 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound324 p)
theorem guard325 (p : Pattern) (guard : pushGuard support p 163 189 215 215 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound325 (p : Pattern) (guard : pushGuard support p 163 189 215 215 = true) : bonus 163 p ≤ 1 + Generated.soko1_2Potential.boulder 215 - Generated.soko1_2Potential.boulder 189 + bonus 189 (change p 189 (some 215)) := by
  have certified := compare897 p (guard325 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 189 (some 215))
  have normalized := agree258 _ _ (change_representative support p 189 (some 215) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check325 (p : Pattern) : (!pushGuard support p 163 189 215 215 || decide (bonus 163 p ≤ 1 + Generated.soko1_2Potential.boulder 215 - Generated.soko1_2Potential.boulder 189 + bonus 189 (change p 189 (some 215)))) = true :=
  check_of_implication _ _ (bound325 p)
theorem guard326 (p : Pattern) (guard : walkGuard soko1_2.board support p 163 164 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound326 (p : Pattern) (guard : walkGuard soko1_2.board support p 163 164 .east = true) : bonus 163 p ≤ bonus 164 p := by
  have certified := compare897 p (guard326 p guard)
  simpa only [at163, at164, Int.zero_add] using certified
theorem check326 (p : Pattern) : (!walkGuard soko1_2.board support p 163 164 .east || decide (bonus 163 p ≤ bonus 164 p)) = true :=
  check_of_implication _ _ (bound326 p)
theorem guard327 (p : Pattern) (guard : walkGuard soko1_2.board support p 163 190 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound327 (p : Pattern) (guard : walkGuard soko1_2.board support p 163 190 .southEast = true) : bonus 163 p ≤ bonus 190 p := by
  have certified := compare897 p (guard327 p guard)
  simpa only [at163, at190, Int.zero_add] using certified
theorem check327 (p : Pattern) : (!walkGuard soko1_2.board support p 163 190 .southEast || decide (bonus 163 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound327 p)
theorem guard328 (p : Pattern) (guard : walkGuard soko1_2.board support p 164 190 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound328 (p : Pattern) (guard : walkGuard soko1_2.board support p 164 190 .south = true) : bonus 164 p ≤ bonus 190 p := by
  have certified := compare897 p (guard328 p guard)
  simpa only [at164, at190, Int.zero_add] using certified
theorem check328 (p : Pattern) : (!walkGuard soko1_2.board support p 164 190 .south || decide (bonus 164 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound328 p)
theorem guard329 (p : Pattern) (guard : pushGuard support p 164 190 216 216 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound329 (p : Pattern) (guard : pushGuard support p 164 190 216 216 = true) : bonus 164 p ≤ 1 + Generated.soko1_2Potential.boulder 216 - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some 216)) := by
  have certified := compare2570 p (guard329 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 190 (some 216))
  have normalized := agree258 _ _ (change_representative support p 190 (some 216) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check329 (p : Pattern) : (!pushGuard support p 164 190 216 216 || decide (bonus 164 p ≤ 1 + Generated.soko1_2Potential.boulder 216 - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some 216)))) = true :=
  check_of_implication _ _ (bound329 p)
theorem guard330 (p : Pattern) (guard : walkGuard soko1_2.board support p 164 163 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound330 (p : Pattern) (guard : walkGuard soko1_2.board support p 164 163 .west = true) : bonus 164 p ≤ bonus 163 p := by
  have certified := compare897 p (guard330 p guard)
  simpa only [at164, at163, Int.zero_add] using certified
theorem check330 (p : Pattern) : (!walkGuard soko1_2.board support p 164 163 .west || decide (bonus 164 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound330 p)
theorem guard331 (p : Pattern) (guard : walkGuard soko1_2.board support p 164 191 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound331 (p : Pattern) (guard : walkGuard soko1_2.board support p 164 191 .southEast = true) : bonus 164 p ≤ bonus 191 p := by
  have certified := compare897 p (guard331 p guard)
  simpa only [at164, at191, Int.zero_add] using certified
theorem check331 (p : Pattern) : (!walkGuard soko1_2.board support p 164 191 .southEast || decide (bonus 164 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound331 p)
theorem guard332 (p : Pattern) (guard : walkGuard soko1_2.board support p 164 189 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound332 (p : Pattern) (guard : walkGuard soko1_2.board support p 164 189 .southWest = true) : bonus 164 p ≤ bonus 189 p := by
  have certified := compare897 p (guard332 p guard)
  simpa only [at164, at189, Int.zero_add] using certified
theorem check332 (p : Pattern) : (!walkGuard soko1_2.board support p 164 189 .southWest || decide (bonus 164 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound332 p)
theorem guard333 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 140 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound333 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 140 .north = true) : bonus 166 p ≤ bonus 140 p := by
  have certified := compare897 p (guard333 p guard)
  simpa only [at166, at140, Int.zero_add] using certified
theorem check333 (p : Pattern) : (!walkGuard soko1_2.board support p 166 140 .north || decide (bonus 166 p ≤ bonus 140 p)) = true :=
  check_of_implication _ _ (bound333 p)
theorem guard334 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 192 .south = true) : d854 p = 1 := by
  change (!false && !(p 192) && !false) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound334 (p : Pattern) (guard : walkGuard soko1_2.board support p 166 192 .south = true) : bonus 166 p ≤ bonus 192 p := by
  have certified := compare2639 p (guard334 p guard)
  simpa only [at166, at192, Int.zero_add] using certified
theorem check334 (p : Pattern) : (!walkGuard soko1_2.board support p 166 192 .south || decide (bonus 166 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound334 p)
theorem guard335 (p : Pattern) (guard : pushGuard support p 166 192 218 218 = true) : d853 p = 1 := by
  change (!false && (!true || (p 192)) && !false && (!false || false)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d853, h192] at guard ⊢
theorem bound335 (p : Pattern) (guard : pushGuard support p 166 192 218 218 = true) : bonus 166 p ≤ 1 + Generated.soko1_2Potential.boulder 218 - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some 218)) := by
  have certified := compare2716 p (guard335 p guard)
  change d258 p ≤ (2 : Int) + d586 (change p 192 (some 218))
  have normalized := agree586 _ _ (change_representative support p 192 (some 218) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d586 (change p 192 none)
  rw [sub1623]
  exact certified
theorem check335 (p : Pattern) : (!pushGuard support p 166 192 218 218 || decide (bonus 166 p ≤ 1 + Generated.soko1_2Potential.boulder 218 - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some 218)))) = true :=
  check_of_implication _ _ (bound335 p)
end NetHack.Sokoban12CostPartition
