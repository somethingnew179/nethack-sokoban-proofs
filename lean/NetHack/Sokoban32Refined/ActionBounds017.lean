import NetHack.Sokoban32Refined.ActionBounds016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard408 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 146 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound408 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 146 .southWest = true) : bonus 121 p ≤ bonus 146 p := by
  have certified := compare103 p (guard408 p guard)
  simpa only [at121, at146, Int.zero_add] using certified
theorem check408 (p : Pattern) : (!walkGuard soko3_2.board support p 121 146 .southWest || decide (bonus 121 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound408 p)
theorem guard409 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 96 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound409 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 96 .north = true) : bonus 122 p ≤ bonus 96 p := by
  have certified := compare103 p (guard409 p guard)
  simpa only [at122, at96, Int.zero_add] using certified
theorem check409 (p : Pattern) : (!walkGuard soko3_2.board support p 122 96 .north || decide (bonus 122 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound409 p)
theorem guard410 (p : Pattern) (guard : pushGuard support p 122 96 70 70 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound410 (p : Pattern) (guard : pushGuard support p 122 96 70 70 = true) : bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some 70)) := by
  have certified := compare37 p (guard410 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 96 (some 70))
  have normalized := agree0 _ _ (change_representative support p 96 (some 70) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check410 (p : Pattern) : (!pushGuard support p 122 96 70 70 || decide (bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some 70)))) = true :=
  check_of_implication _ _ (bound410 p)
theorem guard411 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 148 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound411 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 148 .south = true) : bonus 122 p ≤ bonus 148 p := by
  have certified := compare103 p (guard411 p guard)
  simpa only [at122, at148, Int.zero_add] using certified
theorem check411 (p : Pattern) : (!walkGuard soko3_2.board support p 122 148 .south || decide (bonus 122 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound411 p)
theorem guard412 (p : Pattern) (guard : pushGuard support p 122 148 174 174 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound412 (p : Pattern) (guard : pushGuard support p 122 148 174 174 = true) : bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some 174)) := by
  have certified := compare37 p (guard412 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 148 (some 174))
  have normalized := agree0 _ _ (change_representative support p 148 (some 174) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check412 (p : Pattern) : (!pushGuard support p 122 148 174 174 || decide (bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some 174)))) = true :=
  check_of_implication _ _ (bound412 p)
theorem guard413 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 123 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound413 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 123 .east = true) : bonus 122 p ≤ bonus 123 p := by
  have certified := compare103 p (guard413 p guard)
  simpa only [at122, at123, Int.zero_add] using certified
theorem check413 (p : Pattern) : (!walkGuard soko3_2.board support p 122 123 .east || decide (bonus 122 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound413 p)
theorem guard414 (p : Pattern) (guard : pushGuard support p 122 123 124 124 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound414 (p : Pattern) (guard : pushGuard support p 122 123 124 124 = true) : bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some 124)) := by
  have certified := compare37 p (guard414 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 123 (some 124))
  have normalized := agree0 _ _ (change_representative support p 123 (some 124) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check414 (p : Pattern) : (!pushGuard support p 122 123 124 124 || decide (bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some 124)))) = true :=
  check_of_implication _ _ (bound414 p)
theorem guard415 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 121 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound415 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 121 .west = true) : bonus 122 p ≤ bonus 121 p := by
  have certified := compare103 p (guard415 p guard)
  simpa only [at122, at121, Int.zero_add] using certified
theorem check415 (p : Pattern) : (!walkGuard soko3_2.board support p 122 121 .west || decide (bonus 122 p ≤ bonus 121 p)) = true :=
  check_of_implication _ _ (bound415 p)
theorem guard416 (p : Pattern) (guard : pushGuard support p 122 121 120 120 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound416 (p : Pattern) (guard : pushGuard support p 122 121 120 120 = true) : bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder 120 - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some 120)) := by
  have certified := compare37 p (guard416 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 121 (some 120))
  have normalized := agree0 _ _ (change_representative support p 121 (some 120) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check416 (p : Pattern) : (!pushGuard support p 122 121 120 120 || decide (bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder 120 - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some 120)))) = true :=
  check_of_implication _ _ (bound416 p)
theorem guard417 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 97 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound417 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 97 .northEast = true) : bonus 122 p ≤ bonus 97 p := by
  have certified := compare103 p (guard417 p guard)
  simpa only [at122, at97, Int.zero_add] using certified
theorem check417 (p : Pattern) : (!walkGuard soko3_2.board support p 122 97 .northEast || decide (bonus 122 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound417 p)
theorem guard418 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 95 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound418 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 95 .northWest = true) : bonus 122 p ≤ bonus 95 p := by
  have certified := compare103 p (guard418 p guard)
  simpa only [at122, at95, Int.zero_add] using certified
theorem check418 (p : Pattern) : (!walkGuard soko3_2.board support p 122 95 .northWest || decide (bonus 122 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound418 p)
theorem guard419 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 149 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound419 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 149 .southEast = true) : bonus 122 p ≤ bonus 149 p := by
  have certified := compare103 p (guard419 p guard)
  simpa only [at122, at149, Int.zero_add] using certified
theorem check419 (p : Pattern) : (!walkGuard soko3_2.board support p 122 149 .southEast || decide (bonus 122 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound419 p)
theorem guard420 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 147 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound420 (p : Pattern) (guard : walkGuard soko3_2.board support p 122 147 .southWest = true) : bonus 122 p ≤ bonus 147 p := by
  have certified := compare103 p (guard420 p guard)
  simpa only [at122, at147, Int.zero_add] using certified
theorem check420 (p : Pattern) : (!walkGuard soko3_2.board support p 122 147 .southWest || decide (bonus 122 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound420 p)
theorem guard421 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 97 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound421 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 97 .north = true) : bonus 123 p ≤ bonus 97 p := by
  have certified := compare103 p (guard421 p guard)
  simpa only [at123, at97, Int.zero_add] using certified
theorem check421 (p : Pattern) : (!walkGuard soko3_2.board support p 123 97 .north || decide (bonus 123 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound421 p)
theorem guard422 (p : Pattern) (guard : pushGuard support p 123 97 71 71 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound422 (p : Pattern) (guard : pushGuard support p 123 97 71 71 = true) : bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some 71)) := by
  have certified := compare37 p (guard422 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 97 (some 71))
  have normalized := agree0 _ _ (change_representative support p 97 (some 71) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check422 (p : Pattern) : (!pushGuard support p 123 97 71 71 || decide (bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some 71)))) = true :=
  check_of_implication _ _ (bound422 p)
theorem guard423 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 149 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound423 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 149 .south = true) : bonus 123 p ≤ bonus 149 p := by
  have certified := compare103 p (guard423 p guard)
  simpa only [at123, at149, Int.zero_add] using certified
theorem check423 (p : Pattern) : (!walkGuard soko3_2.board support p 123 149 .south || decide (bonus 123 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound423 p)
theorem guard424 (p : Pattern) (guard : pushGuard support p 123 149 175 175 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound424 (p : Pattern) (guard : pushGuard support p 123 149 175 175 = true) : bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some 175)) := by
  have certified := compare37 p (guard424 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 149 (some 175))
  have normalized := agree0 _ _ (change_representative support p 149 (some 175) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check424 (p : Pattern) : (!pushGuard support p 123 149 175 175 || decide (bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some 175)))) = true :=
  check_of_implication _ _ (bound424 p)
theorem guard425 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 124 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound425 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 124 .east = true) : bonus 123 p ≤ bonus 124 p := by
  have certified := compare103 p (guard425 p guard)
  simpa only [at123, at124, Int.zero_add] using certified
theorem check425 (p : Pattern) : (!walkGuard soko3_2.board support p 123 124 .east || decide (bonus 123 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound425 p)
theorem guard426 (p : Pattern) (guard : pushGuard support p 123 124 125 125 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound426 (p : Pattern) (guard : pushGuard support p 123 124 125 125 = true) : bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some 125)) := by
  have certified := compare37 p (guard426 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 124 (some 125))
  have normalized := agree0 _ _ (change_representative support p 124 (some 125) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check426 (p : Pattern) : (!pushGuard support p 123 124 125 125 || decide (bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some 125)))) = true :=
  check_of_implication _ _ (bound426 p)
theorem guard427 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 122 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound427 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 122 .west = true) : bonus 123 p ≤ bonus 122 p := by
  have certified := compare103 p (guard427 p guard)
  simpa only [at123, at122, Int.zero_add] using certified
theorem check427 (p : Pattern) : (!walkGuard soko3_2.board support p 123 122 .west || decide (bonus 123 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound427 p)
theorem guard428 (p : Pattern) (guard : pushGuard support p 123 122 121 121 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound428 (p : Pattern) (guard : pushGuard support p 123 122 121 121 = true) : bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some 121)) := by
  have certified := compare37 p (guard428 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 122 (some 121))
  have normalized := agree0 _ _ (change_representative support p 122 (some 121) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check428 (p : Pattern) : (!pushGuard support p 123 122 121 121 || decide (bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some 121)))) = true :=
  check_of_implication _ _ (bound428 p)
theorem guard429 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 98 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound429 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 98 .northEast = true) : bonus 123 p ≤ bonus 98 p := by
  have certified := compare103 p (guard429 p guard)
  simpa only [at123, at98, Int.zero_add] using certified
theorem check429 (p : Pattern) : (!walkGuard soko3_2.board support p 123 98 .northEast || decide (bonus 123 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound429 p)
theorem guard430 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 96 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound430 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 96 .northWest = true) : bonus 123 p ≤ bonus 96 p := by
  have certified := compare103 p (guard430 p guard)
  simpa only [at123, at96, Int.zero_add] using certified
theorem check430 (p : Pattern) : (!walkGuard soko3_2.board support p 123 96 .northWest || decide (bonus 123 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound430 p)
theorem guard431 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 150 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound431 (p : Pattern) (guard : walkGuard soko3_2.board support p 123 150 .southEast = true) : bonus 123 p ≤ bonus 150 p := by
  have certified := compare103 p (guard431 p guard)
  simpa only [at123, at150, Int.zero_add] using certified
theorem check431 (p : Pattern) : (!walkGuard soko3_2.board support p 123 150 .southEast || decide (bonus 123 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound431 p)
end NetHack.Sokoban32Refined
