import NetHack.Sokoban22Refined85.ActionBounds014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard360 (p : Pattern) (guard : pushGuard support p 118 96 74 74 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound360 (p : Pattern) (guard : pushGuard support p 118 96 74 74 = true) : bonus 118 p ≤ 1 + Generated.soko2_2Potential.boulder 74 - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some 74)) := by
  have certified := compare20 p (guard360 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 96 (some 74))
  have normalized := agree312 _ _ (change_representative support p 96 (some 74) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check360 (p : Pattern) : (!pushGuard support p 118 96 74 74 || decide (bonus 118 p ≤ 1 + Generated.soko2_2Potential.boulder 74 - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some 74)))) = true :=
  check_of_implication _ _ (bound360 p)
theorem guard361 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 119 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound361 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 119 .east = true) : bonus 118 p ≤ bonus 119 p := by
  have certified := compare19 p (guard361 p guard)
  simpa only [at118, at119, Int.zero_add] using certified
theorem check361 (p : Pattern) : (!walkGuard soko2_2.board support p 118 119 .east || decide (bonus 118 p ≤ bonus 119 p)) = true :=
  check_of_implication _ _ (bound361 p)
theorem guard362 (p : Pattern) (guard : pushGuard support p 118 119 120 120 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound362 (p : Pattern) (guard : pushGuard support p 118 119 120 120 = true) : bonus 118 p ≤ 1 + Generated.soko2_2Potential.boulder 120 - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some 120)) := by
  have certified := compare1114 p (guard362 p guard)
  change d312 p ≤ (2 : Int) + d312 (change p 119 (some 120))
  have normalized := agree312 _ _ (change_representative support p 119 (some 120) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (2 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check362 (p : Pattern) : (!pushGuard support p 118 119 120 120 || decide (bonus 118 p ≤ 1 + Generated.soko2_2Potential.boulder 120 - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some 120)))) = true :=
  check_of_implication _ _ (bound362 p)
theorem guard363 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 97 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound363 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 97 .northEast = true) : bonus 118 p ≤ bonus 97 p := by
  have certified := compare19 p (guard363 p guard)
  simpa only [at118, at97, Int.zero_add] using certified
theorem check363 (p : Pattern) : (!walkGuard soko2_2.board support p 118 97 .northEast || decide (bonus 118 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound363 p)
theorem guard364 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 95 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound364 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 95 .northWest = true) : bonus 118 p ≤ bonus 95 p := by
  have certified := compare19 p (guard364 p guard)
  simpa only [at118, at95, Int.zero_add] using certified
theorem check364 (p : Pattern) : (!walkGuard soko2_2.board support p 118 95 .northWest || decide (bonus 118 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound364 p)
theorem guard365 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 141 .southEast = true) : d4077 p = 1 := by
  change (!false && !(p 141) && !(true && true && false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d4077, h141] at guard ⊢
theorem bound365 (p : Pattern) (guard : walkGuard soko2_2.board support p 118 141 .southEast = true) : bonus 118 p ≤ bonus 141 p := by
  have certified := compare2318 p (guard365 p guard)
  simpa only [at118, at141, Int.zero_add] using certified
theorem check365 (p : Pattern) : (!walkGuard soko2_2.board support p 118 141 .southEast || decide (bonus 118 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound365 p)
theorem guard366 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 97 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound366 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 97 .north = true) : bonus 119 p ≤ bonus 97 p := by
  have certified := compare19 p (guard366 p guard)
  simpa only [at119, at97, Int.zero_add] using certified
theorem check366 (p : Pattern) : (!walkGuard soko2_2.board support p 119 97 .north || decide (bonus 119 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound366 p)
theorem guard367 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 141 .south = true) : d4077 p = 1 := by
  change (!false && !(p 141) && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d4077, h141] at guard ⊢
theorem bound367 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 141 .south = true) : bonus 119 p ≤ bonus 141 p := by
  have certified := compare2318 p (guard367 p guard)
  simpa only [at119, at141, Int.zero_add] using certified
theorem check367 (p : Pattern) : (!walkGuard soko2_2.board support p 119 141 .south || decide (bonus 119 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound367 p)
theorem guard368 (p : Pattern) (guard : pushGuard support p 119 141 163 163 = true) : d4149 p = 1 := by
  change (!false && (!true || (p 141)) && !(p 163) && (!(p 163) || false)) = true at guard
  cases h141 : p 141 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4149, h141, h163] at guard ⊢
theorem bound368 (p : Pattern) (guard : pushGuard support p 119 141 163 163 = true) : bonus 119 p ≤ 1 + Generated.soko2_2Potential.boulder 163 - Generated.soko2_2Potential.boulder 141 + bonus 141 (change p 141 (some 163)) := by
  have certified := compare2457 p (guard368 p guard)
  change d312 p ≤ (0 : Int) + d709 (change p 141 (some 163))
  have normalized := agree709 _ _ (change_representative support p 141 (some 163) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (0 : Int) + d709 (change p 141 (some 163))
  rw [sub3281]
  exact certified
theorem check368 (p : Pattern) : (!pushGuard support p 119 141 163 163 || decide (bonus 119 p ≤ 1 + Generated.soko2_2Potential.boulder 163 - Generated.soko2_2Potential.boulder 141 + bonus 141 (change p 141 (some 163)))) = true :=
  check_of_implication _ _ (bound368 p)
theorem guard369 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 120 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound369 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 120 .east = true) : bonus 119 p ≤ bonus 120 p := by
  have certified := compare19 p (guard369 p guard)
  simpa only [at119, at120, Int.zero_add] using certified
theorem check369 (p : Pattern) : (!walkGuard soko2_2.board support p 119 120 .east || decide (bonus 119 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound369 p)
theorem guard370 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 118 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound370 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 118 .west = true) : bonus 119 p ≤ bonus 118 p := by
  have certified := compare19 p (guard370 p guard)
  simpa only [at119, at118, Int.zero_add] using certified
theorem check370 (p : Pattern) : (!walkGuard soko2_2.board support p 119 118 .west || decide (bonus 119 p ≤ bonus 118 p)) = true :=
  check_of_implication _ _ (bound370 p)
theorem guard371 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 98 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound371 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 98 .northEast = true) : bonus 119 p ≤ bonus 98 p := by
  have certified := compare19 p (guard371 p guard)
  simpa only [at119, at98, Int.zero_add] using certified
theorem check371 (p : Pattern) : (!walkGuard soko2_2.board support p 119 98 .northEast || decide (bonus 119 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound371 p)
theorem guard372 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 96 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound372 (p : Pattern) (guard : walkGuard soko2_2.board support p 119 96 .northWest = true) : bonus 119 p ≤ bonus 96 p := by
  have certified := compare19 p (guard372 p guard)
  simpa only [at119, at96, Int.zero_add] using certified
theorem check372 (p : Pattern) : (!walkGuard soko2_2.board support p 119 96 .northWest || decide (bonus 119 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound372 p)
theorem guard373 (p : Pattern) (guard : walkGuard soko2_2.board support p 120 98 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound373 (p : Pattern) (guard : walkGuard soko2_2.board support p 120 98 .north = true) : bonus 120 p ≤ bonus 98 p := by
  have certified := compare19 p (guard373 p guard)
  simpa only [at120, at98, Int.zero_add] using certified
theorem check373 (p : Pattern) : (!walkGuard soko2_2.board support p 120 98 .north || decide (bonus 120 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound373 p)
theorem guard374 (p : Pattern) (guard : pushGuard support p 120 98 76 76 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound374 (p : Pattern) (guard : pushGuard support p 120 98 76 76 = true) : bonus 120 p ≤ 1 + Generated.soko2_2Potential.boulder 76 - Generated.soko2_2Potential.boulder 98 + bonus 98 (change p 98 (some 76)) := by
  have certified := compare20 p (guard374 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 98 (some 76))
  have normalized := agree312 _ _ (change_representative support p 98 (some 76) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check374 (p : Pattern) : (!pushGuard support p 120 98 76 76 || decide (bonus 120 p ≤ 1 + Generated.soko2_2Potential.boulder 76 - Generated.soko2_2Potential.boulder 98 + bonus 98 (change p 98 (some 76)))) = true :=
  check_of_implication _ _ (bound374 p)
theorem guard375 (p : Pattern) (guard : walkGuard soko2_2.board support p 120 119 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound375 (p : Pattern) (guard : walkGuard soko2_2.board support p 120 119 .west = true) : bonus 120 p ≤ bonus 119 p := by
  have certified := compare19 p (guard375 p guard)
  simpa only [at120, at119, Int.zero_add] using certified
theorem check375 (p : Pattern) : (!walkGuard soko2_2.board support p 120 119 .west || decide (bonus 120 p ≤ bonus 119 p)) = true :=
  check_of_implication _ _ (bound375 p)
theorem guard376 (p : Pattern) (guard : pushGuard support p 120 119 118 118 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound376 (p : Pattern) (guard : pushGuard support p 120 119 118 118 = true) : bonus 120 p ≤ 1 + Generated.soko2_2Potential.boulder 118 - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some 118)) := by
  have certified := compare1114 p (guard376 p guard)
  change d312 p ≤ (2 : Int) + d312 (change p 119 (some 118))
  have normalized := agree312 _ _ (change_representative support p 119 (some 118) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (2 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check376 (p : Pattern) : (!pushGuard support p 120 119 118 118 || decide (bonus 120 p ≤ 1 + Generated.soko2_2Potential.boulder 118 - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some 118)))) = true :=
  check_of_implication _ _ (bound376 p)
theorem guard377 (p : Pattern) (guard : walkGuard soko2_2.board support p 120 97 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound377 (p : Pattern) (guard : walkGuard soko2_2.board support p 120 97 .northWest = true) : bonus 120 p ≤ bonus 97 p := by
  have certified := compare19 p (guard377 p guard)
  simpa only [at120, at97, Int.zero_add] using certified
theorem check377 (p : Pattern) : (!walkGuard soko2_2.board support p 120 97 .northWest || decide (bonus 120 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound377 p)
theorem guard378 (p : Pattern) (guard : walkGuard soko2_2.board support p 120 141 .southWest = true) : d4077 p = 1 := by
  change (!false && !(p 141) && !(true && true && false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d4077, h141] at guard ⊢
theorem bound378 (p : Pattern) (guard : walkGuard soko2_2.board support p 120 141 .southWest = true) : bonus 120 p ≤ bonus 141 p := by
  have certified := compare2318 p (guard378 p guard)
  simpa only [at120, at141, Int.zero_add] using certified
theorem check378 (p : Pattern) : (!walkGuard soko2_2.board support p 120 141 .southWest || decide (bonus 120 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound378 p)
theorem guard379 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 100 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound379 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 100 .north = true) : bonus 122 p ≤ bonus 100 p := by
  have certified := compare1086 p (guard379 p guard)
  simpa only [at122, at100, Int.zero_add] using certified
theorem check379 (p : Pattern) : (!walkGuard soko2_2.board support p 122 100 .north || decide (bonus 122 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound379 p)
theorem guard380 (p : Pattern) (guard : pushGuard support p 122 100 78 78 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound380 (p : Pattern) (guard : pushGuard support p 122 100 78 78 = true) : bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder 78 - Generated.soko2_2Potential.boulder 100 + bonus 100 (change p 100 (some 78)) := by
  have certified := compare1087 p (guard380 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 100 (some 78))
  have normalized := agree0 _ _ (change_representative support p 100 (some 78) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check380 (p : Pattern) : (!pushGuard support p 122 100 78 78 || decide (bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder 78 - Generated.soko2_2Potential.boulder 100 + bonus 100 (change p 100 (some 78)))) = true :=
  check_of_implication _ _ (bound380 p)
theorem guard381 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 144 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound381 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 144 .south = true) : bonus 122 p ≤ bonus 144 p := by
  have certified := compare1086 p (guard381 p guard)
  simpa only [at122, at144, Int.zero_add] using certified
theorem check381 (p : Pattern) : (!walkGuard soko2_2.board support p 122 144 .south || decide (bonus 122 p ≤ bonus 144 p)) = true :=
  check_of_implication _ _ (bound381 p)
theorem guard382 (p : Pattern) (guard : pushGuard support p 122 144 166 166 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound382 (p : Pattern) (guard : pushGuard support p 122 144 166 166 = true) : bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder 166 - Generated.soko2_2Potential.boulder 144 + bonus 144 (change p 144 (some 166)) := by
  have certified := compare1087 p (guard382 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 144 (some 166))
  have normalized := agree0 _ _ (change_representative support p 144 (some 166) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check382 (p : Pattern) : (!pushGuard support p 122 144 166 166 || decide (bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder 166 - Generated.soko2_2Potential.boulder 144 + bonus 144 (change p 144 (some 166)))) = true :=
  check_of_implication _ _ (bound382 p)
theorem guard383 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 123 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound383 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 123 .east = true) : bonus 122 p ≤ bonus 123 p := by
  have certified := compare1086 p (guard383 p guard)
  simpa only [at122, at123, Int.zero_add] using certified
theorem check383 (p : Pattern) : (!walkGuard soko2_2.board support p 122 123 .east || decide (bonus 122 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound383 p)
end NetHack.Sokoban22Refined85
