import NetHack.Sokoban22Refined85.ActionBounds016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard408 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 147 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound408 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 147 .southEast = true) : bonus 124 p ≤ bonus 147 p := by
  have certified := compare1086 p (guard408 p guard)
  simpa only [at124, at147, Int.zero_add] using certified
theorem check408 (p : Pattern) : (!walkGuard soko2_2.board support p 124 147 .southEast || decide (bonus 124 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound408 p)
theorem guard409 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 145 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound409 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 145 .southWest = true) : bonus 124 p ≤ bonus 145 p := by
  have certified := compare1086 p (guard409 p guard)
  simpa only [at124, at145, Int.zero_add] using certified
theorem check409 (p : Pattern) : (!walkGuard soko2_2.board support p 124 145 .southWest || decide (bonus 124 p ≤ bonus 145 p)) = true :=
  check_of_implication _ _ (bound409 p)
theorem guard410 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 103 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound410 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 103 .north = true) : bonus 125 p ≤ bonus 103 p := by
  have certified := compare1086 p (guard410 p guard)
  simpa only [at125, at103, Int.zero_add] using certified
theorem check410 (p : Pattern) : (!walkGuard soko2_2.board support p 125 103 .north || decide (bonus 125 p ≤ bonus 103 p)) = true :=
  check_of_implication _ _ (bound410 p)
theorem guard411 (p : Pattern) (guard : pushGuard support p 125 103 81 81 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound411 (p : Pattern) (guard : pushGuard support p 125 103 81 81 = true) : bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder 81 - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some 81)) := by
  have certified := compare1087 p (guard411 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 103 (some 81))
  have normalized := agree0 _ _ (change_representative support p 103 (some 81) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check411 (p : Pattern) : (!pushGuard support p 125 103 81 81 || decide (bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder 81 - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some 81)))) = true :=
  check_of_implication _ _ (bound411 p)
theorem guard412 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 147 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound412 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 147 .south = true) : bonus 125 p ≤ bonus 147 p := by
  have certified := compare1086 p (guard412 p guard)
  simpa only [at125, at147, Int.zero_add] using certified
theorem check412 (p : Pattern) : (!walkGuard soko2_2.board support p 125 147 .south || decide (bonus 125 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound412 p)
theorem guard413 (p : Pattern) (guard : pushGuard support p 125 147 169 169 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound413 (p : Pattern) (guard : pushGuard support p 125 147 169 169 = true) : bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some 169)) := by
  have certified := compare1087 p (guard413 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 147 (some 169))
  have normalized := agree0 _ _ (change_representative support p 147 (some 169) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check413 (p : Pattern) : (!pushGuard support p 125 147 169 169 || decide (bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some 169)))) = true :=
  check_of_implication _ _ (bound413 p)
theorem guard414 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 126 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound414 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 126 .east = true) : bonus 125 p ≤ bonus 126 p := by
  have certified := compare1086 p (guard414 p guard)
  simpa only [at125, at126, Int.zero_add] using certified
theorem check414 (p : Pattern) : (!walkGuard soko2_2.board support p 125 126 .east || decide (bonus 125 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound414 p)
theorem guard415 (p : Pattern) (guard : pushGuard support p 125 126 127 127 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound415 (p : Pattern) (guard : pushGuard support p 125 126 127 127 = true) : bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some 127)) := by
  have certified := compare1087 p (guard415 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 126 (some 127))
  have normalized := agree0 _ _ (change_representative support p 126 (some 127) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check415 (p : Pattern) : (!pushGuard support p 125 126 127 127 || decide (bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some 127)))) = true :=
  check_of_implication _ _ (bound415 p)
theorem guard416 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 124 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound416 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 124 .west = true) : bonus 125 p ≤ bonus 124 p := by
  have certified := compare1086 p (guard416 p guard)
  simpa only [at125, at124, Int.zero_add] using certified
theorem check416 (p : Pattern) : (!walkGuard soko2_2.board support p 125 124 .west || decide (bonus 125 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound416 p)
theorem guard417 (p : Pattern) (guard : pushGuard support p 125 124 123 123 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound417 (p : Pattern) (guard : pushGuard support p 125 124 123 123 = true) : bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some 123)) := by
  have certified := compare1087 p (guard417 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 124 (some 123))
  have normalized := agree0 _ _ (change_representative support p 124 (some 123) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check417 (p : Pattern) : (!pushGuard support p 125 124 123 123 || decide (bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some 123)))) = true :=
  check_of_implication _ _ (bound417 p)
theorem guard418 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 104 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound418 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 104 .northEast = true) : bonus 125 p ≤ bonus 104 p := by
  have certified := compare1086 p (guard418 p guard)
  simpa only [at125, at104, Int.zero_add] using certified
theorem check418 (p : Pattern) : (!walkGuard soko2_2.board support p 125 104 .northEast || decide (bonus 125 p ≤ bonus 104 p)) = true :=
  check_of_implication _ _ (bound418 p)
theorem guard419 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 102 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound419 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 102 .northWest = true) : bonus 125 p ≤ bonus 102 p := by
  have certified := compare1086 p (guard419 p guard)
  simpa only [at125, at102, Int.zero_add] using certified
theorem check419 (p : Pattern) : (!walkGuard soko2_2.board support p 125 102 .northWest || decide (bonus 125 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound419 p)
theorem guard420 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 148 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound420 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 148 .southEast = true) : bonus 125 p ≤ bonus 148 p := by
  have certified := compare1086 p (guard420 p guard)
  simpa only [at125, at148, Int.zero_add] using certified
theorem check420 (p : Pattern) : (!walkGuard soko2_2.board support p 125 148 .southEast || decide (bonus 125 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound420 p)
theorem guard421 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 146 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound421 (p : Pattern) (guard : walkGuard soko2_2.board support p 125 146 .southWest = true) : bonus 125 p ≤ bonus 146 p := by
  have certified := compare1086 p (guard421 p guard)
  simpa only [at125, at146, Int.zero_add] using certified
theorem check421 (p : Pattern) : (!walkGuard soko2_2.board support p 125 146 .southWest || decide (bonus 125 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound421 p)
theorem guard422 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 104 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound422 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 104 .north = true) : bonus 126 p ≤ bonus 104 p := by
  have certified := compare1086 p (guard422 p guard)
  simpa only [at126, at104, Int.zero_add] using certified
theorem check422 (p : Pattern) : (!walkGuard soko2_2.board support p 126 104 .north || decide (bonus 126 p ≤ bonus 104 p)) = true :=
  check_of_implication _ _ (bound422 p)
theorem guard423 (p : Pattern) (guard : pushGuard support p 126 104 82 82 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound423 (p : Pattern) (guard : pushGuard support p 126 104 82 82 = true) : bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder 82 - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some 82)) := by
  have certified := compare1087 p (guard423 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 104 (some 82))
  have normalized := agree0 _ _ (change_representative support p 104 (some 82) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check423 (p : Pattern) : (!pushGuard support p 126 104 82 82 || decide (bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder 82 - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some 82)))) = true :=
  check_of_implication _ _ (bound423 p)
theorem guard424 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 148 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound424 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 148 .south = true) : bonus 126 p ≤ bonus 148 p := by
  have certified := compare1086 p (guard424 p guard)
  simpa only [at126, at148, Int.zero_add] using certified
theorem check424 (p : Pattern) : (!walkGuard soko2_2.board support p 126 148 .south || decide (bonus 126 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound424 p)
theorem guard425 (p : Pattern) (guard : pushGuard support p 126 148 170 170 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound425 (p : Pattern) (guard : pushGuard support p 126 148 170 170 = true) : bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some 170)) := by
  have certified := compare1087 p (guard425 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 148 (some 170))
  have normalized := agree0 _ _ (change_representative support p 148 (some 170) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check425 (p : Pattern) : (!pushGuard support p 126 148 170 170 || decide (bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some 170)))) = true :=
  check_of_implication _ _ (bound425 p)
theorem guard426 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 127 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound426 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 127 .east = true) : bonus 126 p ≤ bonus 127 p := by
  have certified := compare1086 p (guard426 p guard)
  simpa only [at126, at127, Int.zero_add] using certified
theorem check426 (p : Pattern) : (!walkGuard soko2_2.board support p 126 127 .east || decide (bonus 126 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound426 p)
theorem guard427 (p : Pattern) (guard : pushGuard support p 126 127 128 128 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound427 (p : Pattern) (guard : pushGuard support p 126 127 128 128 = true) : bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder 128 - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some 128)) := by
  have certified := compare1087 p (guard427 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 127 (some 128))
  have normalized := agree0 _ _ (change_representative support p 127 (some 128) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check427 (p : Pattern) : (!pushGuard support p 126 127 128 128 || decide (bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder 128 - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some 128)))) = true :=
  check_of_implication _ _ (bound427 p)
theorem guard428 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 125 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound428 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 125 .west = true) : bonus 126 p ≤ bonus 125 p := by
  have certified := compare1086 p (guard428 p guard)
  simpa only [at126, at125, Int.zero_add] using certified
theorem check428 (p : Pattern) : (!walkGuard soko2_2.board support p 126 125 .west || decide (bonus 126 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound428 p)
theorem guard429 (p : Pattern) (guard : pushGuard support p 126 125 124 124 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound429 (p : Pattern) (guard : pushGuard support p 126 125 124 124 = true) : bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some 124)) := by
  have certified := compare1087 p (guard429 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 125 (some 124))
  have normalized := agree0 _ _ (change_representative support p 125 (some 124) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check429 (p : Pattern) : (!pushGuard support p 126 125 124 124 || decide (bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some 124)))) = true :=
  check_of_implication _ _ (bound429 p)
theorem guard430 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 105 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound430 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 105 .northEast = true) : bonus 126 p ≤ bonus 105 p := by
  have certified := compare1086 p (guard430 p guard)
  simpa only [at126, at105, Int.zero_add] using certified
theorem check430 (p : Pattern) : (!walkGuard soko2_2.board support p 126 105 .northEast || decide (bonus 126 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound430 p)
theorem guard431 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 103 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound431 (p : Pattern) (guard : walkGuard soko2_2.board support p 126 103 .northWest = true) : bonus 126 p ≤ bonus 103 p := by
  have certified := compare1086 p (guard431 p guard)
  simpa only [at126, at103, Int.zero_add] using certified
theorem check431 (p : Pattern) : (!walkGuard soko2_2.board support p 126 103 .northWest || decide (bonus 126 p ≤ bonus 103 p)) = true :=
  check_of_implication _ _ (bound431 p)
end NetHack.Sokoban22Refined85
