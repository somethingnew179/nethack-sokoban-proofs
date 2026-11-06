import NetHack.Sokoban22Refined85.ActionBounds012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard312 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 128 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound312 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 128 .southEast = true) : bonus 105 p ≤ bonus 128 p := by
  have certified := compare1086 p (guard312 p guard)
  simpa only [at105, at128, Int.zero_add] using certified
theorem check312 (p : Pattern) : (!walkGuard soko2_2.board support p 105 128 .southEast || decide (bonus 105 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound312 p)
theorem guard313 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 126 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound313 (p : Pattern) (guard : walkGuard soko2_2.board support p 105 126 .southWest = true) : bonus 105 p ≤ bonus 126 p := by
  have certified := compare1086 p (guard313 p guard)
  simpa only [at105, at126, Int.zero_add] using certified
theorem check313 (p : Pattern) : (!walkGuard soko2_2.board support p 105 126 .southWest || decide (bonus 105 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound313 p)
theorem guard314 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 84 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound314 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 84 .north = true) : bonus 106 p ≤ bonus 84 p := by
  have certified := compare1086 p (guard314 p guard)
  simpa only [at106, at84, Int.zero_add] using certified
theorem check314 (p : Pattern) : (!walkGuard soko2_2.board support p 106 84 .north || decide (bonus 106 p ≤ bonus 84 p)) = true :=
  check_of_implication _ _ (bound314 p)
theorem guard315 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 128 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound315 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 128 .south = true) : bonus 106 p ≤ bonus 128 p := by
  have certified := compare1086 p (guard315 p guard)
  simpa only [at106, at128, Int.zero_add] using certified
theorem check315 (p : Pattern) : (!walkGuard soko2_2.board support p 106 128 .south || decide (bonus 106 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound315 p)
theorem guard316 (p : Pattern) (guard : pushGuard support p 106 128 150 150 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound316 (p : Pattern) (guard : pushGuard support p 106 128 150 150 = true) : bonus 106 p ≤ 1 + Generated.soko2_2Potential.boulder 150 - Generated.soko2_2Potential.boulder 128 + bonus 128 (change p 128 (some 150)) := by
  have certified := compare1087 p (guard316 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 128 (some 150))
  have normalized := agree0 _ _ (change_representative support p 128 (some 150) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check316 (p : Pattern) : (!pushGuard support p 106 128 150 150 || decide (bonus 106 p ≤ 1 + Generated.soko2_2Potential.boulder 150 - Generated.soko2_2Potential.boulder 128 + bonus 128 (change p 128 (some 150)))) = true :=
  check_of_implication _ _ (bound316 p)
theorem guard317 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 105 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound317 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 105 .west = true) : bonus 106 p ≤ bonus 105 p := by
  have certified := compare1086 p (guard317 p guard)
  simpa only [at106, at105, Int.zero_add] using certified
theorem check317 (p : Pattern) : (!walkGuard soko2_2.board support p 106 105 .west || decide (bonus 106 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound317 p)
theorem guard318 (p : Pattern) (guard : pushGuard support p 106 105 104 104 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound318 (p : Pattern) (guard : pushGuard support p 106 105 104 104 = true) : bonus 106 p ≤ 1 + Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some 104)) := by
  have certified := compare1087 p (guard318 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 105 (some 104))
  have normalized := agree0 _ _ (change_representative support p 105 (some 104) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check318 (p : Pattern) : (!pushGuard support p 106 105 104 104 || decide (bonus 106 p ≤ 1 + Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some 104)))) = true :=
  check_of_implication _ _ (bound318 p)
theorem guard319 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 83 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound319 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 83 .northWest = true) : bonus 106 p ≤ bonus 83 p := by
  have certified := compare1086 p (guard319 p guard)
  simpa only [at106, at83, Int.zero_add] using certified
theorem check319 (p : Pattern) : (!walkGuard soko2_2.board support p 106 83 .northWest || decide (bonus 106 p ≤ bonus 83 p)) = true :=
  check_of_implication _ _ (bound319 p)
theorem guard320 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 127 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound320 (p : Pattern) (guard : walkGuard soko2_2.board support p 106 127 .southWest = true) : bonus 106 p ≤ bonus 127 p := by
  have certified := compare1086 p (guard320 p guard)
  simpa only [at106, at127, Int.zero_add] using certified
theorem check320 (p : Pattern) : (!walkGuard soko2_2.board support p 106 127 .southWest || decide (bonus 106 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound320 p)
theorem guard321 (p : Pattern) (guard : walkGuard soko2_2.board support p 111 89 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound321 (p : Pattern) (guard : walkGuard soko2_2.board support p 111 89 .north = true) : bonus 111 p ≤ bonus 89 p := by
  have certified := compare0 p (guard321 p guard)
  simpa only [at111, at89, Int.zero_add] using certified
theorem check321 (p : Pattern) : (!walkGuard soko2_2.board support p 111 89 .north || decide (bonus 111 p ≤ bonus 89 p)) = true :=
  check_of_implication _ _ (bound321 p)
theorem guard322 (p : Pattern) (guard : pushGuard support p 111 89 67 67 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound322 (p : Pattern) (guard : pushGuard support p 111 89 67 67 = true) : bonus 111 p ≤ 1 + Generated.soko2_2Potential.boulder 67 - Generated.soko2_2Potential.boulder 89 + bonus 89 (change p 89 (some 67)) := by
  have certified := compare1 p (guard322 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 89 (some 67))
  have normalized := agree267 _ _ (change_representative support p 89 (some 67) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check322 (p : Pattern) : (!pushGuard support p 111 89 67 67 || decide (bonus 111 p ≤ 1 + Generated.soko2_2Potential.boulder 67 - Generated.soko2_2Potential.boulder 89 + bonus 89 (change p 89 (some 67)))) = true :=
  check_of_implication _ _ (bound322 p)
theorem guard323 (p : Pattern) (guard : walkGuard soko2_2.board support p 111 133 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound323 (p : Pattern) (guard : walkGuard soko2_2.board support p 111 133 .south = true) : bonus 111 p ≤ bonus 133 p := by
  have certified := compare0 p (guard323 p guard)
  simpa only [at111, at133, Int.zero_add] using certified
theorem check323 (p : Pattern) : (!walkGuard soko2_2.board support p 111 133 .south || decide (bonus 111 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound323 p)
theorem guard324 (p : Pattern) (guard : pushGuard support p 111 133 155 155 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound324 (p : Pattern) (guard : pushGuard support p 111 133 155 155 = true) : bonus 111 p ≤ 1 + Generated.soko2_2Potential.boulder 155 - Generated.soko2_2Potential.boulder 133 + bonus 133 (change p 133 (some 155)) := by
  have certified := compare1 p (guard324 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 133 (some 155))
  have normalized := agree267 _ _ (change_representative support p 133 (some 155) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check324 (p : Pattern) : (!pushGuard support p 111 133 155 155 || decide (bonus 111 p ≤ 1 + Generated.soko2_2Potential.boulder 155 - Generated.soko2_2Potential.boulder 133 + bonus 133 (change p 133 (some 155)))) = true :=
  check_of_implication _ _ (bound324 p)
theorem guard325 (p : Pattern) (guard : walkGuard soko2_2.board support p 111 90 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound325 (p : Pattern) (guard : walkGuard soko2_2.board support p 111 90 .northEast = true) : bonus 111 p ≤ bonus 90 p := by
  have certified := compare0 p (guard325 p guard)
  simpa only [at111, at90, Int.zero_add] using certified
theorem check325 (p : Pattern) : (!walkGuard soko2_2.board support p 111 90 .northEast || decide (bonus 111 p ≤ bonus 90 p)) = true :=
  check_of_implication _ _ (bound325 p)
theorem guard326 (p : Pattern) (guard : walkGuard soko2_2.board support p 111 134 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound326 (p : Pattern) (guard : walkGuard soko2_2.board support p 111 134 .southEast = true) : bonus 111 p ≤ bonus 134 p := by
  have certified := compare0 p (guard326 p guard)
  simpa only [at111, at134, Int.zero_add] using certified
theorem check326 (p : Pattern) : (!walkGuard soko2_2.board support p 111 134 .southEast || decide (bonus 111 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound326 p)
theorem guard327 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 91 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound327 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 91 .north = true) : bonus 113 p ≤ bonus 91 p := by
  have certified := compare0 p (guard327 p guard)
  simpa only [at113, at91, Int.zero_add] using certified
theorem check327 (p : Pattern) : (!walkGuard soko2_2.board support p 113 91 .north || decide (bonus 113 p ≤ bonus 91 p)) = true :=
  check_of_implication _ _ (bound327 p)
theorem guard328 (p : Pattern) (guard : pushGuard support p 113 91 69 69 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound328 (p : Pattern) (guard : pushGuard support p 113 91 69 69 = true) : bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder 69 - Generated.soko2_2Potential.boulder 91 + bonus 91 (change p 91 (some 69)) := by
  have certified := compare1 p (guard328 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 91 (some 69))
  have normalized := agree267 _ _ (change_representative support p 91 (some 69) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check328 (p : Pattern) : (!pushGuard support p 113 91 69 69 || decide (bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder 69 - Generated.soko2_2Potential.boulder 91 + bonus 91 (change p 91 (some 69)))) = true :=
  check_of_implication _ _ (bound328 p)
theorem guard329 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 135 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound329 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 135 .south = true) : bonus 113 p ≤ bonus 135 p := by
  have certified := compare0 p (guard329 p guard)
  simpa only [at113, at135, Int.zero_add] using certified
theorem check329 (p : Pattern) : (!walkGuard soko2_2.board support p 113 135 .south || decide (bonus 113 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound329 p)
theorem guard330 (p : Pattern) (guard : pushGuard support p 113 135 157 157 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound330 (p : Pattern) (guard : pushGuard support p 113 135 157 157 = true) : bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder 157 - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some 157)) := by
  have certified := compare0 p (guard330 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 135 (some 157))
  have normalized := agree267 _ _ (change_representative support p 135 (some 157) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check330 (p : Pattern) : (!pushGuard support p 113 135 157 157 || decide (bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder 157 - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some 157)))) = true :=
  check_of_implication _ _ (bound330 p)
theorem guard331 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 114 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound331 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 114 .east = true) : bonus 113 p ≤ bonus 114 p := by
  have certified := compare0 p (guard331 p guard)
  simpa only [at113, at114, Int.zero_add] using certified
theorem check331 (p : Pattern) : (!walkGuard soko2_2.board support p 113 114 .east || decide (bonus 113 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound331 p)
theorem guard332 (p : Pattern) (guard : pushGuard support p 113 114 115 115 = true) : d4058 p = 1 := by
  change (!false && (!false || false) && !(p 115) && (!(p 115) || false)) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound332 (p : Pattern) (guard : pushGuard support p 113 114 115 115 = true) : bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder 115 - Generated.soko2_2Potential.boulder 114 + bonus 114 (change p 114 (some 115)) := by
  have certified := compare1477 p (guard332 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 114 (some 115))
  have normalized := agree267 _ _ (change_representative support p 114 (some 115) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 (some 115))
  rw [sub2500]
  exact certified
theorem check332 (p : Pattern) : (!pushGuard support p 113 114 115 115 || decide (bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder 115 - Generated.soko2_2Potential.boulder 114 + bonus 114 (change p 114 (some 115)))) = true :=
  check_of_implication _ _ (bound332 p)
theorem guard333 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 90 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound333 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 90 .northWest = true) : bonus 113 p ≤ bonus 90 p := by
  have certified := compare0 p (guard333 p guard)
  simpa only [at113, at90, Int.zero_add] using certified
theorem check333 (p : Pattern) : (!walkGuard soko2_2.board support p 113 90 .northWest || decide (bonus 113 p ≤ bonus 90 p)) = true :=
  check_of_implication _ _ (bound333 p)
theorem guard334 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 136 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound334 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 136 .southEast = true) : bonus 113 p ≤ bonus 136 p := by
  have certified := compare0 p (guard334 p guard)
  simpa only [at113, at136, Int.zero_add] using certified
theorem check334 (p : Pattern) : (!walkGuard soko2_2.board support p 113 136 .southEast || decide (bonus 113 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound334 p)
theorem guard335 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 134 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound335 (p : Pattern) (guard : walkGuard soko2_2.board support p 113 134 .southWest = true) : bonus 113 p ≤ bonus 134 p := by
  have certified := compare0 p (guard335 p guard)
  simpa only [at113, at134, Int.zero_add] using certified
theorem check335 (p : Pattern) : (!walkGuard soko2_2.board support p 113 134 .southWest || decide (bonus 113 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound335 p)
end NetHack.Sokoban22Refined85
