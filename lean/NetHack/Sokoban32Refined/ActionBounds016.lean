import NetHack.Sokoban32Refined.ActionBounds015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard384 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 138 .southWest = true) : d1126 p = 1 := by
  change (!(p 113) && !(p 138) && !(true && (p 139) && (p 112))) = true at guard
  cases h112 : p 112 <;> cases h113 : p 113 <;> cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d857, d1088, d1092, d1122, d1125, d1126, h112, h113, h138, h139] at guard ⊢
theorem bound384 (p : Pattern) (guard : walkGuard soko3_2.board support p 113 138 .southWest = true) : bonus 113 p ≤ bonus 138 p := by
  have certified := compare2136 p (guard384 p guard)
  simpa only [at113, at138, Int.zero_add] using certified
theorem check384 (p : Pattern) : (!walkGuard soko3_2.board support p 113 138 .southWest || decide (bonus 113 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound384 p)
theorem guard385 (p : Pattern) (guard : walkGuard soko3_2.board support p 114 88 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound385 (p : Pattern) (guard : walkGuard soko3_2.board support p 114 88 .north = true) : bonus 114 p ≤ bonus 88 p := by
  have certified := compare0 p (guard385 p guard)
  simpa only [at114, at88, Int.zero_add] using certified
theorem check385 (p : Pattern) : (!walkGuard soko3_2.board support p 114 88 .north || decide (bonus 114 p ≤ bonus 88 p)) = true :=
  check_of_implication _ _ (bound385 p)
theorem guard386 (p : Pattern) (guard : pushGuard support p 114 88 62 62 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound386 (p : Pattern) (guard : pushGuard support p 114 88 62 62 = true) : bonus 114 p ≤ 1 + Generated.soko3_2Potential.boulder 62 - Generated.soko3_2Potential.boulder 88 + bonus 88 (change p 88 (some 62)) := by
  have certified := compare104 p (guard386 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 88 (some 62))
  have normalized := agree134 _ _ (change_representative support p 88 (some 62) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check386 (p : Pattern) : (!pushGuard support p 114 88 62 62 || decide (bonus 114 p ≤ 1 + Generated.soko3_2Potential.boulder 62 - Generated.soko3_2Potential.boulder 88 + bonus 88 (change p 88 (some 62)))) = true :=
  check_of_implication _ _ (bound386 p)
theorem guard387 (p : Pattern) (guard : walkGuard soko3_2.board support p 114 113 .west = true) : d866 p = 1 := by
  change (!false && !(p 113) && !false) = true at guard
  cases h113 : p 113
  all_goals simp [d0, d1, d866, h113] at guard ⊢
theorem bound387 (p : Pattern) (guard : walkGuard soko3_2.board support p 114 113 .west = true) : bonus 114 p ≤ bonus 113 p := by
  have certified := compare535 p (guard387 p guard)
  simpa only [at114, at113, Int.zero_add] using certified
theorem check387 (p : Pattern) : (!walkGuard soko3_2.board support p 114 113 .west || decide (bonus 114 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound387 p)
theorem guard388 (p : Pattern) (guard : pushGuard support p 114 113 112 112 = true) : d1073 p = 1 := by
  change (!false && (!true || (p 113)) && !(p 112) && (!(p 112) || false)) = true at guard
  cases h112 : p 112 <;> cases h113 : p 113
  all_goals simp [d0, d1, d865, d1073, h112, h113] at guard ⊢
theorem bound388 (p : Pattern) (guard : pushGuard support p 114 113 112 112 = true) : bonus 114 p ≤ 1 + Generated.soko3_2Potential.boulder 112 - Generated.soko3_2Potential.boulder 113 + bonus 113 (change p 113 (some 112)) := by
  have certified := compare2208 p (guard388 p guard)
  change d134 p ≤ (0 : Int) + d255 (change p 113 (some 112))
  have normalized := agree255 _ _ (change_representative support p 113 (some 112) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d255 (change p 113 (some 112))
  rw [sub1441]
  exact certified
theorem check388 (p : Pattern) : (!pushGuard support p 114 113 112 112 || decide (bonus 114 p ≤ 1 + Generated.soko3_2Potential.boulder 112 - Generated.soko3_2Potential.boulder 113 + bonus 113 (change p 113 (some 112)))) = true :=
  check_of_implication _ _ (bound388 p)
theorem guard389 (p : Pattern) (guard : walkGuard soko3_2.board support p 114 139 .southWest = true) : d1095 p = 1 := by
  change (!false && !(p 139) && !(true && true && (p 113))) = true at guard
  cases h113 : p 113 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1095, h113, h139] at guard ⊢
theorem bound389 (p : Pattern) (guard : walkGuard soko3_2.board support p 114 139 .southWest = true) : bonus 114 p ≤ bonus 139 p := by
  have certified := compare2252 p (guard389 p guard)
  simpa only [at114, at139, Int.zero_add] using certified
theorem check389 (p : Pattern) : (!walkGuard soko3_2.board support p 114 139 .southWest || decide (bonus 114 p ≤ bonus 139 p)) = true :=
  check_of_implication _ _ (bound389 p)
theorem guard390 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 94 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound390 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 94 .north = true) : bonus 120 p ≤ bonus 94 p := by
  have certified := compare103 p (guard390 p guard)
  simpa only [at120, at94, Int.zero_add] using certified
theorem check390 (p : Pattern) : (!walkGuard soko3_2.board support p 120 94 .north || decide (bonus 120 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound390 p)
theorem guard391 (p : Pattern) (guard : pushGuard support p 120 94 68 68 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound391 (p : Pattern) (guard : pushGuard support p 120 94 68 68 = true) : bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder 68 - Generated.soko3_2Potential.boulder 94 + bonus 94 (change p 94 (some 68)) := by
  have certified := compare37 p (guard391 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 94 (some 68))
  have normalized := agree0 _ _ (change_representative support p 94 (some 68) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check391 (p : Pattern) : (!pushGuard support p 120 94 68 68 || decide (bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder 68 - Generated.soko3_2Potential.boulder 94 + bonus 94 (change p 94 (some 68)))) = true :=
  check_of_implication _ _ (bound391 p)
theorem guard392 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 146 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound392 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 146 .south = true) : bonus 120 p ≤ bonus 146 p := by
  have certified := compare103 p (guard392 p guard)
  simpa only [at120, at146, Int.zero_add] using certified
theorem check392 (p : Pattern) : (!walkGuard soko3_2.board support p 120 146 .south || decide (bonus 120 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound392 p)
theorem guard393 (p : Pattern) (guard : pushGuard support p 120 146 172 172 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound393 (p : Pattern) (guard : pushGuard support p 120 146 172 172 = true) : bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder 172 - Generated.soko3_2Potential.boulder 146 + bonus 146 (change p 146 (some 172)) := by
  have certified := compare37 p (guard393 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 146 (some 172))
  have normalized := agree0 _ _ (change_representative support p 146 (some 172) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check393 (p : Pattern) : (!pushGuard support p 120 146 172 172 || decide (bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder 172 - Generated.soko3_2Potential.boulder 146 + bonus 146 (change p 146 (some 172)))) = true :=
  check_of_implication _ _ (bound393 p)
theorem guard394 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 121 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound394 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 121 .east = true) : bonus 120 p ≤ bonus 121 p := by
  have certified := compare103 p (guard394 p guard)
  simpa only [at120, at121, Int.zero_add] using certified
theorem check394 (p : Pattern) : (!walkGuard soko3_2.board support p 120 121 .east || decide (bonus 120 p ≤ bonus 121 p)) = true :=
  check_of_implication _ _ (bound394 p)
theorem guard395 (p : Pattern) (guard : pushGuard support p 120 121 122 122 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound395 (p : Pattern) (guard : pushGuard support p 120 121 122 122 = true) : bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some 122)) := by
  have certified := compare37 p (guard395 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 121 (some 122))
  have normalized := agree0 _ _ (change_representative support p 121 (some 122) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check395 (p : Pattern) : (!pushGuard support p 120 121 122 122 || decide (bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some 122)))) = true :=
  check_of_implication _ _ (bound395 p)
theorem guard396 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 95 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound396 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 95 .northEast = true) : bonus 120 p ≤ bonus 95 p := by
  have certified := compare103 p (guard396 p guard)
  simpa only [at120, at95, Int.zero_add] using certified
theorem check396 (p : Pattern) : (!walkGuard soko3_2.board support p 120 95 .northEast || decide (bonus 120 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound396 p)
theorem guard397 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 147 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound397 (p : Pattern) (guard : walkGuard soko3_2.board support p 120 147 .southEast = true) : bonus 120 p ≤ bonus 147 p := by
  have certified := compare103 p (guard397 p guard)
  simpa only [at120, at147, Int.zero_add] using certified
theorem check397 (p : Pattern) : (!walkGuard soko3_2.board support p 120 147 .southEast || decide (bonus 120 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound397 p)
theorem guard398 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 95 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound398 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 95 .north = true) : bonus 121 p ≤ bonus 95 p := by
  have certified := compare103 p (guard398 p guard)
  simpa only [at121, at95, Int.zero_add] using certified
theorem check398 (p : Pattern) : (!walkGuard soko3_2.board support p 121 95 .north || decide (bonus 121 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound398 p)
theorem guard399 (p : Pattern) (guard : pushGuard support p 121 95 69 69 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound399 (p : Pattern) (guard : pushGuard support p 121 95 69 69 = true) : bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder 69 - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some 69)) := by
  have certified := compare37 p (guard399 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 95 (some 69))
  have normalized := agree0 _ _ (change_representative support p 95 (some 69) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check399 (p : Pattern) : (!pushGuard support p 121 95 69 69 || decide (bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder 69 - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some 69)))) = true :=
  check_of_implication _ _ (bound399 p)
theorem guard400 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 147 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound400 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 147 .south = true) : bonus 121 p ≤ bonus 147 p := by
  have certified := compare103 p (guard400 p guard)
  simpa only [at121, at147, Int.zero_add] using certified
theorem check400 (p : Pattern) : (!walkGuard soko3_2.board support p 121 147 .south || decide (bonus 121 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound400 p)
theorem guard401 (p : Pattern) (guard : pushGuard support p 121 147 173 173 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound401 (p : Pattern) (guard : pushGuard support p 121 147 173 173 = true) : bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some 173)) := by
  have certified := compare37 p (guard401 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 147 (some 173))
  have normalized := agree0 _ _ (change_representative support p 147 (some 173) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check401 (p : Pattern) : (!pushGuard support p 121 147 173 173 || decide (bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some 173)))) = true :=
  check_of_implication _ _ (bound401 p)
theorem guard402 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 122 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound402 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 122 .east = true) : bonus 121 p ≤ bonus 122 p := by
  have certified := compare103 p (guard402 p guard)
  simpa only [at121, at122, Int.zero_add] using certified
theorem check402 (p : Pattern) : (!walkGuard soko3_2.board support p 121 122 .east || decide (bonus 121 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound402 p)
theorem guard403 (p : Pattern) (guard : pushGuard support p 121 122 123 123 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound403 (p : Pattern) (guard : pushGuard support p 121 122 123 123 = true) : bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some 123)) := by
  have certified := compare37 p (guard403 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 122 (some 123))
  have normalized := agree0 _ _ (change_representative support p 122 (some 123) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check403 (p : Pattern) : (!pushGuard support p 121 122 123 123 || decide (bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some 123)))) = true :=
  check_of_implication _ _ (bound403 p)
theorem guard404 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 120 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound404 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 120 .west = true) : bonus 121 p ≤ bonus 120 p := by
  have certified := compare103 p (guard404 p guard)
  simpa only [at121, at120, Int.zero_add] using certified
theorem check404 (p : Pattern) : (!walkGuard soko3_2.board support p 121 120 .west || decide (bonus 121 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound404 p)
theorem guard405 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 96 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound405 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 96 .northEast = true) : bonus 121 p ≤ bonus 96 p := by
  have certified := compare103 p (guard405 p guard)
  simpa only [at121, at96, Int.zero_add] using certified
theorem check405 (p : Pattern) : (!walkGuard soko3_2.board support p 121 96 .northEast || decide (bonus 121 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound405 p)
theorem guard406 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 94 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound406 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 94 .northWest = true) : bonus 121 p ≤ bonus 94 p := by
  have certified := compare103 p (guard406 p guard)
  simpa only [at121, at94, Int.zero_add] using certified
theorem check406 (p : Pattern) : (!walkGuard soko3_2.board support p 121 94 .northWest || decide (bonus 121 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound406 p)
theorem guard407 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 148 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound407 (p : Pattern) (guard : walkGuard soko3_2.board support p 121 148 .southEast = true) : bonus 121 p ≤ bonus 148 p := by
  have certified := compare103 p (guard407 p guard)
  simpa only [at121, at148, Int.zero_add] using certified
theorem check407 (p : Pattern) : (!walkGuard soko3_2.board support p 121 148 .southEast || decide (bonus 121 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound407 p)
end NetHack.Sokoban32Refined
