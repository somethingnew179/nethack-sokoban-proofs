import NetHack.Sokoban32Refined.ActionBounds012
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard312 (p : Pattern) (guard : pushGuard support p 100 101 102 102 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound312 (p : Pattern) (guard : pushGuard support p 100 101 102 102 = true) : bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder 102 - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some 102)) := by
  have certified := compare37 p (guard312 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 101 (some 102))
  have normalized := agree0 _ _ (change_representative support p 101 (some 102) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check312 (p : Pattern) : (!pushGuard support p 100 101 102 102 || decide (bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder 102 - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some 102)))) = true :=
  check_of_implication _ _ (bound312 p)
theorem guard313 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 99 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound313 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 99 .west = true) : bonus 100 p ≤ bonus 99 p := by
  have certified := compare103 p (guard313 p guard)
  simpa only [at100, at99, Int.zero_add] using certified
theorem check313 (p : Pattern) : (!walkGuard soko3_2.board support p 100 99 .west || decide (bonus 100 p ≤ bonus 99 p)) = true :=
  check_of_implication _ _ (bound313 p)
theorem guard314 (p : Pattern) (guard : pushGuard support p 100 99 98 98 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound314 (p : Pattern) (guard : pushGuard support p 100 99 98 98 = true) : bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some 98)) := by
  have certified := compare37 p (guard314 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 99 (some 98))
  have normalized := agree0 _ _ (change_representative support p 99 (some 98) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check314 (p : Pattern) : (!pushGuard support p 100 99 98 98 || decide (bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some 98)))) = true :=
  check_of_implication _ _ (bound314 p)
theorem guard315 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 75 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound315 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 75 .northEast = true) : bonus 100 p ≤ bonus 75 p := by
  have certified := compare103 p (guard315 p guard)
  simpa only [at100, at75, Int.zero_add] using certified
theorem check315 (p : Pattern) : (!walkGuard soko3_2.board support p 100 75 .northEast || decide (bonus 100 p ≤ bonus 75 p)) = true :=
  check_of_implication _ _ (bound315 p)
theorem guard316 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 73 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound316 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 73 .northWest = true) : bonus 100 p ≤ bonus 73 p := by
  have certified := compare103 p (guard316 p guard)
  simpa only [at100, at73, Int.zero_add] using certified
theorem check316 (p : Pattern) : (!walkGuard soko3_2.board support p 100 73 .northWest || decide (bonus 100 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound316 p)
theorem guard317 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 127 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound317 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 127 .southEast = true) : bonus 100 p ≤ bonus 127 p := by
  have certified := compare103 p (guard317 p guard)
  simpa only [at100, at127, Int.zero_add] using certified
theorem check317 (p : Pattern) : (!walkGuard soko3_2.board support p 100 127 .southEast || decide (bonus 100 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound317 p)
theorem guard318 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 125 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound318 (p : Pattern) (guard : walkGuard soko3_2.board support p 100 125 .southWest = true) : bonus 100 p ≤ bonus 125 p := by
  have certified := compare103 p (guard318 p guard)
  simpa only [at100, at125, Int.zero_add] using certified
theorem check318 (p : Pattern) : (!walkGuard soko3_2.board support p 100 125 .southWest || decide (bonus 100 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound318 p)
theorem guard319 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 75 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound319 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 75 .north = true) : bonus 101 p ≤ bonus 75 p := by
  have certified := compare103 p (guard319 p guard)
  simpa only [at101, at75, Int.zero_add] using certified
theorem check319 (p : Pattern) : (!walkGuard soko3_2.board support p 101 75 .north || decide (bonus 101 p ≤ bonus 75 p)) = true :=
  check_of_implication _ _ (bound319 p)
theorem guard320 (p : Pattern) (guard : pushGuard support p 101 75 49 49 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound320 (p : Pattern) (guard : pushGuard support p 101 75 49 49 = true) : bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder 49 - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some 49)) := by
  have certified := compare37 p (guard320 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 75 (some 49))
  have normalized := agree0 _ _ (change_representative support p 75 (some 49) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check320 (p : Pattern) : (!pushGuard support p 101 75 49 49 || decide (bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder 49 - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some 49)))) = true :=
  check_of_implication _ _ (bound320 p)
theorem guard321 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 127 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound321 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 127 .south = true) : bonus 101 p ≤ bonus 127 p := by
  have certified := compare103 p (guard321 p guard)
  simpa only [at101, at127, Int.zero_add] using certified
theorem check321 (p : Pattern) : (!walkGuard soko3_2.board support p 101 127 .south || decide (bonus 101 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound321 p)
theorem guard322 (p : Pattern) (guard : pushGuard support p 101 127 153 153 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound322 (p : Pattern) (guard : pushGuard support p 101 127 153 153 = true) : bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some 153)) := by
  have certified := compare37 p (guard322 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 127 (some 153))
  have normalized := agree0 _ _ (change_representative support p 127 (some 153) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check322 (p : Pattern) : (!pushGuard support p 101 127 153 153 || decide (bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some 153)))) = true :=
  check_of_implication _ _ (bound322 p)
theorem guard323 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 102 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound323 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 102 .east = true) : bonus 101 p ≤ bonus 102 p := by
  have certified := compare103 p (guard323 p guard)
  simpa only [at101, at102, Int.zero_add] using certified
theorem check323 (p : Pattern) : (!walkGuard soko3_2.board support p 101 102 .east || decide (bonus 101 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound323 p)
theorem guard324 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 100 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound324 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 100 .west = true) : bonus 101 p ≤ bonus 100 p := by
  have certified := compare103 p (guard324 p guard)
  simpa only [at101, at100, Int.zero_add] using certified
theorem check324 (p : Pattern) : (!walkGuard soko3_2.board support p 101 100 .west || decide (bonus 101 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound324 p)
theorem guard325 (p : Pattern) (guard : pushGuard support p 101 100 99 99 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound325 (p : Pattern) (guard : pushGuard support p 101 100 99 99 = true) : bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some 99)) := by
  have certified := compare37 p (guard325 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 100 (some 99))
  have normalized := agree0 _ _ (change_representative support p 100 (some 99) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check325 (p : Pattern) : (!pushGuard support p 101 100 99 99 || decide (bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some 99)))) = true :=
  check_of_implication _ _ (bound325 p)
theorem guard326 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 76 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound326 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 76 .northEast = true) : bonus 101 p ≤ bonus 76 p := by
  have certified := compare103 p (guard326 p guard)
  simpa only [at101, at76, Int.zero_add] using certified
theorem check326 (p : Pattern) : (!walkGuard soko3_2.board support p 101 76 .northEast || decide (bonus 101 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound326 p)
theorem guard327 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 74 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound327 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 74 .northWest = true) : bonus 101 p ≤ bonus 74 p := by
  have certified := compare103 p (guard327 p guard)
  simpa only [at101, at74, Int.zero_add] using certified
theorem check327 (p : Pattern) : (!walkGuard soko3_2.board support p 101 74 .northWest || decide (bonus 101 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound327 p)
theorem guard328 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 128 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound328 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 128 .southEast = true) : bonus 101 p ≤ bonus 128 p := by
  have certified := compare103 p (guard328 p guard)
  simpa only [at101, at128, Int.zero_add] using certified
theorem check328 (p : Pattern) : (!walkGuard soko3_2.board support p 101 128 .southEast || decide (bonus 101 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound328 p)
theorem guard329 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 126 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound329 (p : Pattern) (guard : walkGuard soko3_2.board support p 101 126 .southWest = true) : bonus 101 p ≤ bonus 126 p := by
  have certified := compare103 p (guard329 p guard)
  simpa only [at101, at126, Int.zero_add] using certified
theorem check329 (p : Pattern) : (!walkGuard soko3_2.board support p 101 126 .southWest || decide (bonus 101 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound329 p)
theorem guard330 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 76 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound330 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 76 .north = true) : bonus 102 p ≤ bonus 76 p := by
  have certified := compare103 p (guard330 p guard)
  simpa only [at102, at76, Int.zero_add] using certified
theorem check330 (p : Pattern) : (!walkGuard soko3_2.board support p 102 76 .north || decide (bonus 102 p ≤ bonus 76 p)) = true :=
  check_of_implication _ _ (bound330 p)
theorem guard331 (p : Pattern) (guard : pushGuard support p 102 76 50 50 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound331 (p : Pattern) (guard : pushGuard support p 102 76 50 50 = true) : bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder 50 - Generated.soko3_2Potential.boulder 76 + bonus 76 (change p 76 (some 50)) := by
  have certified := compare37 p (guard331 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 76 (some 50))
  have normalized := agree0 _ _ (change_representative support p 76 (some 50) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check331 (p : Pattern) : (!pushGuard support p 102 76 50 50 || decide (bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder 50 - Generated.soko3_2Potential.boulder 76 + bonus 76 (change p 76 (some 50)))) = true :=
  check_of_implication _ _ (bound331 p)
theorem guard332 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 128 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound332 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 128 .south = true) : bonus 102 p ≤ bonus 128 p := by
  have certified := compare103 p (guard332 p guard)
  simpa only [at102, at128, Int.zero_add] using certified
theorem check332 (p : Pattern) : (!walkGuard soko3_2.board support p 102 128 .south || decide (bonus 102 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound332 p)
theorem guard333 (p : Pattern) (guard : pushGuard support p 102 128 154 154 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound333 (p : Pattern) (guard : pushGuard support p 102 128 154 154 = true) : bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder 154 - Generated.soko3_2Potential.boulder 128 + bonus 128 (change p 128 (some 154)) := by
  have certified := compare37 p (guard333 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 128 (some 154))
  have normalized := agree0 _ _ (change_representative support p 128 (some 154) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check333 (p : Pattern) : (!pushGuard support p 102 128 154 154 || decide (bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder 154 - Generated.soko3_2Potential.boulder 128 + bonus 128 (change p 128 (some 154)))) = true :=
  check_of_implication _ _ (bound333 p)
theorem guard334 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 101 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound334 (p : Pattern) (guard : walkGuard soko3_2.board support p 102 101 .west = true) : bonus 102 p ≤ bonus 101 p := by
  have certified := compare103 p (guard334 p guard)
  simpa only [at102, at101, Int.zero_add] using certified
theorem check334 (p : Pattern) : (!walkGuard soko3_2.board support p 102 101 .west || decide (bonus 102 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound334 p)
theorem guard335 (p : Pattern) (guard : pushGuard support p 102 101 100 100 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound335 (p : Pattern) (guard : pushGuard support p 102 101 100 100 = true) : bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some 100)) := by
  have certified := compare37 p (guard335 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 101 (some 100))
  have normalized := agree0 _ _ (change_representative support p 101 (some 100) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check335 (p : Pattern) : (!pushGuard support p 102 101 100 100 || decide (bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some 100)))) = true :=
  check_of_implication _ _ (bound335 p)
end NetHack.Sokoban32Refined
