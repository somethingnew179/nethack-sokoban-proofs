import NetHack.Sokoban22Refined85.ActionBounds015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard384 (p : Pattern) (guard : pushGuard support p 122 123 124 124 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound384 (p : Pattern) (guard : pushGuard support p 122 123 124 124 = true) : bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some 124)) := by
  have certified := compare1087 p (guard384 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 123 (some 124))
  have normalized := agree0 _ _ (change_representative support p 123 (some 124) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check384 (p : Pattern) : (!pushGuard support p 122 123 124 124 || decide (bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some 124)))) = true :=
  check_of_implication _ _ (bound384 p)
theorem guard385 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 101 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound385 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 101 .northEast = true) : bonus 122 p ≤ bonus 101 p := by
  have certified := compare1086 p (guard385 p guard)
  simpa only [at122, at101, Int.zero_add] using certified
theorem check385 (p : Pattern) : (!walkGuard soko2_2.board support p 122 101 .northEast || decide (bonus 122 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound385 p)
theorem guard386 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 145 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound386 (p : Pattern) (guard : walkGuard soko2_2.board support p 122 145 .southEast = true) : bonus 122 p ≤ bonus 145 p := by
  have certified := compare1086 p (guard386 p guard)
  simpa only [at122, at145, Int.zero_add] using certified
theorem check386 (p : Pattern) : (!walkGuard soko2_2.board support p 122 145 .southEast || decide (bonus 122 p ≤ bonus 145 p)) = true :=
  check_of_implication _ _ (bound386 p)
theorem guard387 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 101 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound387 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 101 .north = true) : bonus 123 p ≤ bonus 101 p := by
  have certified := compare1086 p (guard387 p guard)
  simpa only [at123, at101, Int.zero_add] using certified
theorem check387 (p : Pattern) : (!walkGuard soko2_2.board support p 123 101 .north || decide (bonus 123 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound387 p)
theorem guard388 (p : Pattern) (guard : pushGuard support p 123 101 79 79 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound388 (p : Pattern) (guard : pushGuard support p 123 101 79 79 = true) : bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder 79 - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some 79)) := by
  have certified := compare1087 p (guard388 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 101 (some 79))
  have normalized := agree0 _ _ (change_representative support p 101 (some 79) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check388 (p : Pattern) : (!pushGuard support p 123 101 79 79 || decide (bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder 79 - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some 79)))) = true :=
  check_of_implication _ _ (bound388 p)
theorem guard389 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 145 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound389 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 145 .south = true) : bonus 123 p ≤ bonus 145 p := by
  have certified := compare1086 p (guard389 p guard)
  simpa only [at123, at145, Int.zero_add] using certified
theorem check389 (p : Pattern) : (!walkGuard soko2_2.board support p 123 145 .south || decide (bonus 123 p ≤ bonus 145 p)) = true :=
  check_of_implication _ _ (bound389 p)
theorem guard390 (p : Pattern) (guard : pushGuard support p 123 145 167 167 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound390 (p : Pattern) (guard : pushGuard support p 123 145 167 167 = true) : bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some 167)) := by
  have certified := compare1087 p (guard390 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 145 (some 167))
  have normalized := agree0 _ _ (change_representative support p 145 (some 167) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check390 (p : Pattern) : (!pushGuard support p 123 145 167 167 || decide (bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some 167)))) = true :=
  check_of_implication _ _ (bound390 p)
theorem guard391 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 124 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound391 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 124 .east = true) : bonus 123 p ≤ bonus 124 p := by
  have certified := compare1086 p (guard391 p guard)
  simpa only [at123, at124, Int.zero_add] using certified
theorem check391 (p : Pattern) : (!walkGuard soko2_2.board support p 123 124 .east || decide (bonus 123 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound391 p)
theorem guard392 (p : Pattern) (guard : pushGuard support p 123 124 125 125 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound392 (p : Pattern) (guard : pushGuard support p 123 124 125 125 = true) : bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some 125)) := by
  have certified := compare1087 p (guard392 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 124 (some 125))
  have normalized := agree0 _ _ (change_representative support p 124 (some 125) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check392 (p : Pattern) : (!pushGuard support p 123 124 125 125 || decide (bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some 125)))) = true :=
  check_of_implication _ _ (bound392 p)
theorem guard393 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 122 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound393 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 122 .west = true) : bonus 123 p ≤ bonus 122 p := by
  have certified := compare1086 p (guard393 p guard)
  simpa only [at123, at122, Int.zero_add] using certified
theorem check393 (p : Pattern) : (!walkGuard soko2_2.board support p 123 122 .west || decide (bonus 123 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound393 p)
theorem guard394 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 102 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound394 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 102 .northEast = true) : bonus 123 p ≤ bonus 102 p := by
  have certified := compare1086 p (guard394 p guard)
  simpa only [at123, at102, Int.zero_add] using certified
theorem check394 (p : Pattern) : (!walkGuard soko2_2.board support p 123 102 .northEast || decide (bonus 123 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound394 p)
theorem guard395 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 100 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound395 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 100 .northWest = true) : bonus 123 p ≤ bonus 100 p := by
  have certified := compare1086 p (guard395 p guard)
  simpa only [at123, at100, Int.zero_add] using certified
theorem check395 (p : Pattern) : (!walkGuard soko2_2.board support p 123 100 .northWest || decide (bonus 123 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound395 p)
theorem guard396 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 146 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound396 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 146 .southEast = true) : bonus 123 p ≤ bonus 146 p := by
  have certified := compare1086 p (guard396 p guard)
  simpa only [at123, at146, Int.zero_add] using certified
theorem check396 (p : Pattern) : (!walkGuard soko2_2.board support p 123 146 .southEast || decide (bonus 123 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound396 p)
theorem guard397 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 144 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound397 (p : Pattern) (guard : walkGuard soko2_2.board support p 123 144 .southWest = true) : bonus 123 p ≤ bonus 144 p := by
  have certified := compare1086 p (guard397 p guard)
  simpa only [at123, at144, Int.zero_add] using certified
theorem check397 (p : Pattern) : (!walkGuard soko2_2.board support p 123 144 .southWest || decide (bonus 123 p ≤ bonus 144 p)) = true :=
  check_of_implication _ _ (bound397 p)
theorem guard398 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 102 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound398 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 102 .north = true) : bonus 124 p ≤ bonus 102 p := by
  have certified := compare1086 p (guard398 p guard)
  simpa only [at124, at102, Int.zero_add] using certified
theorem check398 (p : Pattern) : (!walkGuard soko2_2.board support p 124 102 .north || decide (bonus 124 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound398 p)
theorem guard399 (p : Pattern) (guard : pushGuard support p 124 102 80 80 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound399 (p : Pattern) (guard : pushGuard support p 124 102 80 80 = true) : bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder 80 - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some 80)) := by
  have certified := compare1087 p (guard399 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 102 (some 80))
  have normalized := agree0 _ _ (change_representative support p 102 (some 80) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check399 (p : Pattern) : (!pushGuard support p 124 102 80 80 || decide (bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder 80 - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some 80)))) = true :=
  check_of_implication _ _ (bound399 p)
theorem guard400 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 146 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound400 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 146 .south = true) : bonus 124 p ≤ bonus 146 p := by
  have certified := compare1086 p (guard400 p guard)
  simpa only [at124, at146, Int.zero_add] using certified
theorem check400 (p : Pattern) : (!walkGuard soko2_2.board support p 124 146 .south || decide (bonus 124 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound400 p)
theorem guard401 (p : Pattern) (guard : pushGuard support p 124 146 168 168 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound401 (p : Pattern) (guard : pushGuard support p 124 146 168 168 = true) : bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some 168)) := by
  have certified := compare1087 p (guard401 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 146 (some 168))
  have normalized := agree0 _ _ (change_representative support p 146 (some 168) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check401 (p : Pattern) : (!pushGuard support p 124 146 168 168 || decide (bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some 168)))) = true :=
  check_of_implication _ _ (bound401 p)
theorem guard402 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 125 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound402 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 125 .east = true) : bonus 124 p ≤ bonus 125 p := by
  have certified := compare1086 p (guard402 p guard)
  simpa only [at124, at125, Int.zero_add] using certified
theorem check402 (p : Pattern) : (!walkGuard soko2_2.board support p 124 125 .east || decide (bonus 124 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound402 p)
theorem guard403 (p : Pattern) (guard : pushGuard support p 124 125 126 126 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound403 (p : Pattern) (guard : pushGuard support p 124 125 126 126 = true) : bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some 126)) := by
  have certified := compare1087 p (guard403 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 125 (some 126))
  have normalized := agree0 _ _ (change_representative support p 125 (some 126) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check403 (p : Pattern) : (!pushGuard support p 124 125 126 126 || decide (bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some 126)))) = true :=
  check_of_implication _ _ (bound403 p)
theorem guard404 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 123 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound404 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 123 .west = true) : bonus 124 p ≤ bonus 123 p := by
  have certified := compare1086 p (guard404 p guard)
  simpa only [at124, at123, Int.zero_add] using certified
theorem check404 (p : Pattern) : (!walkGuard soko2_2.board support p 124 123 .west || decide (bonus 124 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound404 p)
theorem guard405 (p : Pattern) (guard : pushGuard support p 124 123 122 122 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound405 (p : Pattern) (guard : pushGuard support p 124 123 122 122 = true) : bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder 122 - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some 122)) := by
  have certified := compare1087 p (guard405 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 123 (some 122))
  have normalized := agree0 _ _ (change_representative support p 123 (some 122) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check405 (p : Pattern) : (!pushGuard support p 124 123 122 122 || decide (bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder 122 - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some 122)))) = true :=
  check_of_implication _ _ (bound405 p)
theorem guard406 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 103 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound406 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 103 .northEast = true) : bonus 124 p ≤ bonus 103 p := by
  have certified := compare1086 p (guard406 p guard)
  simpa only [at124, at103, Int.zero_add] using certified
theorem check406 (p : Pattern) : (!walkGuard soko2_2.board support p 124 103 .northEast || decide (bonus 124 p ≤ bonus 103 p)) = true :=
  check_of_implication _ _ (bound406 p)
theorem guard407 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 101 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound407 (p : Pattern) (guard : walkGuard soko2_2.board support p 124 101 .northWest = true) : bonus 124 p ≤ bonus 101 p := by
  have certified := compare1086 p (guard407 p guard)
  simpa only [at124, at101, Int.zero_add] using certified
theorem check407 (p : Pattern) : (!walkGuard soko2_2.board support p 124 101 .northWest || decide (bonus 124 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound407 p)
end NetHack.Sokoban22Refined85
