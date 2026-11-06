import NetHack.Sokoban22Refined85.ActionBounds013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard336 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 136 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound336 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 136 .south = true) : bonus 114 p ≤ bonus 136 p := by
  have certified := compare0 p (guard336 p guard)
  simpa only [at114, at136, Int.zero_add] using certified
theorem check336 (p : Pattern) : (!walkGuard soko2_2.board support p 114 136 .south || decide (bonus 114 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound336 p)
theorem guard337 (p : Pattern) (guard : pushGuard support p 114 136 158 158 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound337 (p : Pattern) (guard : pushGuard support p 114 136 158 158 = true) : bonus 114 p ≤ 1 + Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.boulder 136 + bonus 136 (change p 136 (some 158)) := by
  have certified := compare0 p (guard337 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 136 (some 158))
  have normalized := agree267 _ _ (change_representative support p 136 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check337 (p : Pattern) : (!pushGuard support p 114 136 158 158 || decide (bonus 114 p ≤ 1 + Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.boulder 136 + bonus 136 (change p 136 (some 158)))) = true :=
  check_of_implication _ _ (bound337 p)
theorem guard338 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 115 .east = true) : d4058 p = 1 := by
  change (!false && !(p 115) && !false) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound338 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 115 .east = true) : bonus 114 p ≤ bonus 115 p := by
  have certified := compare1485 p (guard338 p guard)
  simpa only [at114, at115, Int.zero_add] using certified
theorem check338 (p : Pattern) : (!walkGuard soko2_2.board support p 114 115 .east || decide (bonus 114 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound338 p)
theorem guard339 (p : Pattern) (guard : pushGuard support p 114 115 116 116 = true) : d4103 p = 1 := by
  change (!false && (!true || (p 115)) && !(p 116) && (!(p 116) || false)) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116
  all_goals simp [d0, d1, d4066, d4103, h115, h116] at guard ⊢
theorem bound339 (p : Pattern) (guard : pushGuard support p 114 115 116 116 = true) : bonus 114 p ≤ 1 + Generated.soko2_2Potential.boulder 116 - Generated.soko2_2Potential.boulder 115 + bonus 115 (change p 115 (some 116)) := by
  have certified := compare1695 p (guard339 p guard)
  change d267 p ≤ (0 : Int) + d498 (change p 115 (some 116))
  have normalized := agree498 _ _ (change_representative support p 115 (some 116) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d498 (change p 115 (some 116))
  rw [sub2631]
  exact certified
theorem check339 (p : Pattern) : (!pushGuard support p 114 115 116 116 || decide (bonus 114 p ≤ 1 + Generated.soko2_2Potential.boulder 116 - Generated.soko2_2Potential.boulder 115 + bonus 115 (change p 115 (some 116)))) = true :=
  check_of_implication _ _ (bound339 p)
theorem guard340 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 113 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound340 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 113 .west = true) : bonus 114 p ≤ bonus 113 p := by
  have certified := compare0 p (guard340 p guard)
  simpa only [at114, at113, Int.zero_add] using certified
theorem check340 (p : Pattern) : (!walkGuard soko2_2.board support p 114 113 .west || decide (bonus 114 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound340 p)
theorem guard341 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 93 .northEast = true) : d4058 p = 1 := by
  change (!false && !false && !(true && true && (p 115))) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound341 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 93 .northEast = true) : bonus 114 p ≤ bonus 93 p := by
  have certified := compare1703 p (guard341 p guard)
  simpa only [at114, at93, Int.zero_add] using certified
theorem check341 (p : Pattern) : (!walkGuard soko2_2.board support p 114 93 .northEast || decide (bonus 114 p ≤ bonus 93 p)) = true :=
  check_of_implication _ _ (bound341 p)
theorem guard342 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 91 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound342 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 91 .northWest = true) : bonus 114 p ≤ bonus 91 p := by
  have certified := compare0 p (guard342 p guard)
  simpa only [at114, at91, Int.zero_add] using certified
theorem check342 (p : Pattern) : (!walkGuard soko2_2.board support p 114 91 .northWest || decide (bonus 114 p ≤ bonus 91 p)) = true :=
  check_of_implication _ _ (bound342 p)
theorem guard343 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 135 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound343 (p : Pattern) (guard : walkGuard soko2_2.board support p 114 135 .southWest = true) : bonus 114 p ≤ bonus 135 p := by
  have certified := compare0 p (guard343 p guard)
  simpa only [at114, at135, Int.zero_add] using certified
theorem check343 (p : Pattern) : (!walkGuard soko2_2.board support p 114 135 .southWest || decide (bonus 114 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound343 p)
theorem guard344 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 93 .north = true) : d4058 p = 1 := by
  change (!(p 115) && !false && !false) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound344 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 93 .north = true) : bonus 115 p ≤ bonus 93 p := by
  have certified := compare1717 p (guard344 p guard)
  simpa only [at115, at93, Int.zero_add] using certified
theorem check344 (p : Pattern) : (!walkGuard soko2_2.board support p 115 93 .north || decide (bonus 115 p ≤ bonus 93 p)) = true :=
  check_of_implication _ _ (bound344 p)
theorem guard345 (p : Pattern) (guard : pushGuard support p 115 93 71 71 = true) : d4059 p = 1 := by
  change (!(p 115) && (!false || false) && !(p 71) && (!(p 71) || false)) = true at guard
  cases h71 : p 71 <;> cases h115 : p 115
  all_goals simp [d0, d1, d4058, d4059, h71, h115] at guard ⊢
theorem bound345 (p : Pattern) (guard : pushGuard support p 115 93 71 71 = true) : bonus 115 p ≤ 1 + Generated.soko2_2Potential.boulder 71 - Generated.soko2_2Potential.boulder 93 + bonus 93 (change p 93 (some 71)) := by
  have certified := compare1856 p (guard345 p guard)
  change d498 p ≤ (2 : Int) + d312 (change p 93 (some 71))
  have normalized := agree312 _ _ (change_representative support p 93 (some 71) 10000 dummy_outside)
  rw [normalized]
  change d498 p ≤ (2 : Int) + d312 (change p 10000 (some 71))
  rw [sub2676]
  exact certified
theorem check345 (p : Pattern) : (!pushGuard support p 115 93 71 71 || decide (bonus 115 p ≤ 1 + Generated.soko2_2Potential.boulder 71 - Generated.soko2_2Potential.boulder 93 + bonus 93 (change p 93 (some 71)))) = true :=
  check_of_implication _ _ (bound345 p)
theorem guard346 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 116 .east = true) : d4111 p = 1 := by
  change (!(p 115) && !(p 116) && !false) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116
  all_goals simp [d0, d1, d4066, d4111, h115, h116] at guard ⊢
theorem bound346 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 116 .east = true) : bonus 115 p ≤ bonus 116 p := by
  have certified := compare1870 p (guard346 p guard)
  simpa only [at115, at116, Int.zero_add] using certified
theorem check346 (p : Pattern) : (!walkGuard soko2_2.board support p 115 116 .east || decide (bonus 115 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound346 p)
theorem guard347 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 114 .west = true) : d4058 p = 1 := by
  change (!(p 115) && !false && !false) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound347 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 114 .west = true) : bonus 115 p ≤ bonus 114 p := by
  have certified := compare1878 p (guard347 p guard)
  simpa only [at115, at114, Int.zero_add] using certified
theorem check347 (p : Pattern) : (!walkGuard soko2_2.board support p 115 114 .west || decide (bonus 115 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound347 p)
theorem guard348 (p : Pattern) (guard : pushGuard support p 115 114 113 113 = true) : d4058 p = 1 := by
  change (!(p 115) && (!false || false) && !false && (!false || false)) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound348 (p : Pattern) (guard : pushGuard support p 115 114 113 113 = true) : bonus 115 p ≤ 1 + Generated.soko2_2Potential.boulder 113 - Generated.soko2_2Potential.boulder 114 + bonus 114 (change p 114 (some 113)) := by
  have certified := compare1895 p (guard348 p guard)
  change d498 p ≤ (2 : Int) + d267 (change p 114 (some 113))
  have normalized := agree267 _ _ (change_representative support p 114 (some 113) 10000 dummy_outside)
  rw [normalized]
  change d498 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check348 (p : Pattern) : (!pushGuard support p 115 114 113 113 || decide (bonus 115 p ≤ 1 + Generated.soko2_2Potential.boulder 113 - Generated.soko2_2Potential.boulder 114 + bonus 114 (change p 114 (some 113)))) = true :=
  check_of_implication _ _ (bound348 p)
theorem guard349 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 94 .northEast = true) : d4058 p = 1 := by
  change (!(p 115) && !false && !(true && false && (p 116))) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116
  all_goals simp [d0, d1, d4058, h115, h116] at guard ⊢
theorem bound349 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 94 .northEast = true) : bonus 115 p ≤ bonus 94 p := by
  have certified := compare1717 p (guard349 p guard)
  simpa only [at115, at94, Int.zero_add] using certified
theorem check349 (p : Pattern) : (!walkGuard soko2_2.board support p 115 94 .northEast || decide (bonus 115 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound349 p)
theorem guard350 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 138 .southEast = true) : d4114 p = 1 := by
  change (!(p 115) && !(p 138) && !(true && true && (p 116))) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116 <;> cases h138 : p 138
  all_goals simp [d0, d1, d4068, d4113, d4114, h115, h116, h138] at guard ⊢
theorem bound350 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 138 .southEast = true) : bonus 115 p ≤ bonus 138 p := by
  have certified := compare1931 p (guard350 p guard)
  simpa only [at115, at138, Int.zero_add] using certified
theorem check350 (p : Pattern) : (!walkGuard soko2_2.board support p 115 138 .southEast || decide (bonus 115 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound350 p)
theorem guard351 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 136 .southWest = true) : d4058 p = 1 := by
  change (!(p 115) && !false && !(true && true && false)) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound351 (p : Pattern) (guard : walkGuard soko2_2.board support p 115 136 .southWest = true) : bonus 115 p ≤ bonus 136 p := by
  have certified := compare1878 p (guard351 p guard)
  simpa only [at115, at136, Int.zero_add] using certified
theorem check351 (p : Pattern) : (!walkGuard soko2_2.board support p 115 136 .southWest || decide (bonus 115 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound351 p)
theorem guard352 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 94 .north = true) : d4066 p = 1 := by
  change (!(p 116) && !false && !false) = true at guard
  cases h116 : p 116
  all_goals simp [d0, d1, d4066, h116] at guard ⊢
theorem bound352 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 94 .north = true) : bonus 116 p ≤ bonus 94 p := by
  have certified := compare1957 p (guard352 p guard)
  simpa only [at116, at94, Int.zero_add] using certified
theorem check352 (p : Pattern) : (!walkGuard soko2_2.board support p 116 94 .north || decide (bonus 116 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound352 p)
theorem guard353 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 138 .south = true) : d4113 p = 1 := by
  change (!(p 116) && !(p 138) && !false) = true at guard
  cases h116 : p 116 <;> cases h138 : p 138
  all_goals simp [d0, d1, d4068, d4113, h116, h138] at guard ⊢
theorem bound353 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 138 .south = true) : bonus 116 p ≤ bonus 138 p := by
  have certified := compare1996 p (guard353 p guard)
  simpa only [at116, at138, Int.zero_add] using certified
theorem check353 (p : Pattern) : (!walkGuard soko2_2.board support p 116 138 .south || decide (bonus 116 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound353 p)
theorem guard354 (p : Pattern) (guard : pushGuard support p 116 138 160 160 = true) : d4119 p = 1 := by
  change (!(p 116) && (!true || (p 138)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h116 : p 116 <;> cases h138 : p 138 <;> cases h160 : p 160
  all_goals simp [d0, d1, d4117, d4118, d4119, h116, h138, h160] at guard ⊢
theorem bound354 (p : Pattern) (guard : pushGuard support p 116 138 160 160 = true) : bonus 116 p ≤ 1 + Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.boulder 138 + bonus 138 (change p 138 (some 160)) := by
  have certified := compare2122 p (guard354 p guard)
  change d516 p ≤ (0 : Int) + d652 (change p 138 (some 160))
  have normalized := agree652 _ _ (change_representative support p 138 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d516 p ≤ (0 : Int) + d652 (change p 138 (some 160))
  rw [sub2931]
  exact certified
theorem check354 (p : Pattern) : (!pushGuard support p 116 138 160 160 || decide (bonus 116 p ≤ 1 + Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.boulder 138 + bonus 138 (change p 138 (some 160)))) = true :=
  check_of_implication _ _ (bound354 p)
theorem guard355 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 115 .west = true) : d4111 p = 1 := by
  change (!(p 116) && !(p 115) && !false) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116
  all_goals simp [d0, d1, d4066, d4111, h115, h116] at guard ⊢
theorem bound355 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 115 .west = true) : bonus 116 p ≤ bonus 115 p := by
  have certified := compare2136 p (guard355 p guard)
  simpa only [at116, at115, Int.zero_add] using certified
theorem check355 (p : Pattern) : (!walkGuard soko2_2.board support p 116 115 .west || decide (bonus 116 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound355 p)
theorem guard356 (p : Pattern) (guard : pushGuard support p 116 115 114 114 = true) : d4103 p = 1 := by
  change (!(p 116) && (!true || (p 115)) && !false && (!false || false)) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116
  all_goals simp [d0, d1, d4066, d4103, h115, h116] at guard ⊢
theorem bound356 (p : Pattern) (guard : pushGuard support p 116 115 114 114 = true) : bonus 116 p ≤ 1 + Generated.soko2_2Potential.boulder 114 - Generated.soko2_2Potential.boulder 115 + bonus 115 (change p 115 (some 114)) := by
  have certified := compare2230 p (guard356 p guard)
  change d516 p ≤ (2 : Int) + d498 (change p 115 (some 114))
  have normalized := agree498 _ _ (change_representative support p 115 (some 114) 10000 dummy_outside)
  rw [normalized]
  change d516 p ≤ (2 : Int) + d498 (change p 115 none)
  rw [sub3117]
  exact certified
theorem check356 (p : Pattern) : (!pushGuard support p 116 115 114 114 || decide (bonus 116 p ≤ 1 + Generated.soko2_2Potential.boulder 114 - Generated.soko2_2Potential.boulder 115 + bonus 115 (change p 115 (some 114)))) = true :=
  check_of_implication _ _ (bound356 p)
theorem guard357 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 95 .northEast = true) : d4066 p = 1 := by
  change (!(p 116) && !false && !(true && false && true)) = true at guard
  cases h116 : p 116
  all_goals simp [d0, d1, d4066, h116] at guard ⊢
theorem bound357 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 95 .northEast = true) : bonus 116 p ≤ bonus 95 p := by
  have certified := compare1957 p (guard357 p guard)
  simpa only [at116, at95, Int.zero_add] using certified
theorem check357 (p : Pattern) : (!walkGuard soko2_2.board support p 116 95 .northEast || decide (bonus 116 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound357 p)
theorem guard358 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 93 .northWest = true) : d4066 p = 1 := by
  change (!(p 116) && !false && !(true && false && (p 115))) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116
  all_goals simp [d0, d1, d4066, h115, h116] at guard ⊢
theorem bound358 (p : Pattern) (guard : walkGuard soko2_2.board support p 116 93 .northWest = true) : bonus 116 p ≤ bonus 93 p := by
  have certified := compare1957 p (guard358 p guard)
  simpa only [at116, at93, Int.zero_add] using certified
theorem check358 (p : Pattern) : (!walkGuard soko2_2.board support p 116 93 .northWest || decide (bonus 116 p ≤ bonus 93 p)) = true :=
  check_of_implication _ _ (bound358 p)
theorem guard359 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 96 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound359 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 96 .north = true) : bonus 118 p ≤ bonus 96 p := by
  have certified := compare19 p (guard359 p guard)
  simpa only [at118, at96, Int.zero_add] using certified
theorem check359 (p : Pattern) : (!walkGuard soko2_2.board support p 118 96 .north || decide (bonus 118 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound359 p)
end NetHack.Sokoban22Refined85
