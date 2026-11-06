import NetHack.Sokoban12CostPartition.ActionBounds015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard384 (p : Pattern) (guard : pushGuard support p 185 211 237 237 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound384 (p : Pattern) (guard : pushGuard support p 185 211 237 237 = true) : bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some 237)) := by
  have certified := compare2570 p (guard384 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 211 (some 237))
  have normalized := agree258 _ _ (change_representative support p 211 (some 237) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check384 (p : Pattern) : (!pushGuard support p 185 211 237 237 || decide (bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some 237)))) = true :=
  check_of_implication _ _ (bound384 p)
theorem guard385 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 186 .east = true) : d829 p = 1 := by
  change (!false && !(p 186) && !false) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound385 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 186 .east = true) : bonus 185 p ≤ bonus 186 p := by
  have certified := compare3692 p (guard385 p guard)
  simpa only [at185, at186, Int.zero_add] using certified
theorem check385 (p : Pattern) : (!walkGuard soko1_2.board support p 185 186 .east || decide (bonus 185 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound385 p)
theorem guard386 (p : Pattern) (guard : pushGuard support p 185 186 187 187 = true) : d1158 p = 1 := by
  change (!false && (!true || (p 186)) && !(p 187) && (!(p 187) || false)) = true at guard
  cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d851, d1158, h186, h187] at guard ⊢
theorem bound386 (p : Pattern) (guard : pushGuard support p 185 186 187 187 = true) : bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder 187 - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some 187)) := by
  have certified := compare3777 p (guard386 p guard)
  change d258 p ≤ (4 : Int) + d485 (change p 186 (some 187))
  have normalized := agree485 _ _ (change_representative support p 186 (some 187) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (4 : Int) + d485 (change p 186 (some 187))
  rw [sub2021]
  exact certified
theorem check386 (p : Pattern) : (!pushGuard support p 185 186 187 187 || decide (bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder 187 - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some 187)))) = true :=
  check_of_implication _ _ (bound386 p)
theorem guard387 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 184 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound387 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 184 .west = true) : bonus 185 p ≤ bonus 184 p := by
  have certified := compare897 p (guard387 p guard)
  simpa only [at185, at184, Int.zero_add] using certified
theorem check387 (p : Pattern) : (!walkGuard soko1_2.board support p 185 184 .west || decide (bonus 185 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound387 p)
theorem guard388 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 160 .northEast = true) : d1050 p = 1 := by
  change (!false && !(p 160) && !(true && (p 159) && (p 186))) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d758, d829, d1016, d1050, h159, h160, h186] at guard ⊢
theorem bound388 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 160 .northEast = true) : bonus 185 p ≤ bonus 160 p := by
  have certified := compare3827 p (guard388 p guard)
  simpa only [at185, at160, Int.zero_add] using certified
theorem check388 (p : Pattern) : (!walkGuard soko1_2.board support p 185 160 .northEast || decide (bonus 185 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound388 p)
theorem guard389 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 158 .northWest = true) : d742 p = 1 := by
  change (!false && !(p 158) && !(true && (p 159) && false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d742, h158, h159] at guard ⊢
theorem bound389 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 158 .northWest = true) : bonus 185 p ≤ bonus 158 p := by
  have certified := compare3459 p (guard389 p guard)
  simpa only [at185, at158, Int.zero_add] using certified
theorem check389 (p : Pattern) : (!walkGuard soko1_2.board support p 185 158 .northWest || decide (bonus 185 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound389 p)
theorem guard390 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 212 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 186))) = true at guard
  cases h186 : p 186
  all_goals simp [d1, h186] at guard ⊢
theorem bound390 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 212 .southEast = true) : bonus 185 p ≤ bonus 212 p := by
  have certified := compare897 p (guard390 p guard)
  simpa only [at185, at212, Int.zero_add] using certified
theorem check390 (p : Pattern) : (!walkGuard soko1_2.board support p 185 212 .southEast || decide (bonus 185 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound390 p)
theorem guard391 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 210 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound391 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 210 .southWest = true) : bonus 185 p ≤ bonus 210 p := by
  have certified := compare897 p (guard391 p guard)
  simpa only [at185, at210, Int.zero_add] using certified
theorem check391 (p : Pattern) : (!walkGuard soko1_2.board support p 185 210 .southWest || decide (bonus 185 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound391 p)
theorem guard392 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 160 .north = true) : d1016 p = 1 := by
  change (!(p 186) && !(p 160) && !false) = true at guard
  cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d829, d1016, h160, h186] at guard ⊢
theorem bound392 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 160 .north = true) : bonus 186 p ≤ bonus 160 p := by
  have certified := compare3869 p (guard392 p guard)
  simpa only [at186, at160, Int.zero_add] using certified
theorem check392 (p : Pattern) : (!walkGuard soko1_2.board support p 186 160 .north || decide (bonus 186 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound392 p)
theorem guard393 (p : Pattern) (guard : pushGuard support p 186 160 134 134 = true) : d831 p = 1 := by
  change (!(p 186) && (!true || (p 160)) && !(p 134) && (!(p 134) || false)) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d829, d830, d831, h134, h160, h186] at guard ⊢
theorem bound393 (p : Pattern) (guard : pushGuard support p 186 160 134 134 = true) : bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some 134)) := by
  have certified := compare3909 p (guard393 p guard)
  change d485 p ≤ (0 : Int) + d374 (change p 160 (some 134))
  have normalized := agree374 _ _ (change_representative support p 160 (some 134) 10000 dummy_outside)
  rw [normalized]
  change d485 p ≤ (0 : Int) + d374 (change p 160 (some 134))
  rw [sub2056]
  exact certified
theorem check393 (p : Pattern) : (!pushGuard support p 186 160 134 134 || decide (bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some 134)))) = true :=
  check_of_implication _ _ (bound393 p)
theorem guard394 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 212 .south = true) : d829 p = 1 := by
  change (!(p 186) && !false && !false) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound394 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 212 .south = true) : bonus 186 p ≤ bonus 212 p := by
  have certified := compare3961 p (guard394 p guard)
  simpa only [at186, at212, Int.zero_add] using certified
theorem check394 (p : Pattern) : (!walkGuard soko1_2.board support p 186 212 .south || decide (bonus 186 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound394 p)
theorem guard395 (p : Pattern) (guard : pushGuard support p 186 212 238 238 = true) : d829 p = 1 := by
  change (!(p 186) && (!false || false) && !false && (!false || false)) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound395 (p : Pattern) (guard : pushGuard support p 186 212 238 238 = true) : bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some 238)) := by
  have certified := compare4019 p (guard395 p guard)
  change d485 p ≤ (2 : Int) + d258 (change p 212 (some 238))
  have normalized := agree258 _ _ (change_representative support p 212 (some 238) 10000 dummy_outside)
  rw [normalized]
  change d485 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check395 (p : Pattern) : (!pushGuard support p 186 212 238 238 || decide (bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some 238)))) = true :=
  check_of_implication _ _ (bound395 p)
theorem guard396 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 187 .east = true) : d1053 p = 1 := by
  change (!(p 186) && !(p 187) && !false) = true at guard
  cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d851, d1053, h186, h187] at guard ⊢
theorem bound396 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 187 .east = true) : bonus 186 p ≤ bonus 187 p := by
  have certified := compare4062 p (guard396 p guard)
  simpa only [at186, at187, Int.zero_add] using certified
theorem check396 (p : Pattern) : (!walkGuard soko1_2.board support p 186 187 .east || decide (bonus 186 p ≤ bonus 187 p)) = true :=
  check_of_implication _ _ (bound396 p)
theorem guard397 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 185 .west = true) : d829 p = 1 := by
  change (!(p 186) && !false && !false) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound397 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 185 .west = true) : bonus 186 p ≤ bonus 185 p := by
  have certified := compare3961 p (guard397 p guard)
  simpa only [at186, at185, Int.zero_add] using certified
theorem check397 (p : Pattern) : (!walkGuard soko1_2.board support p 186 185 .west || decide (bonus 186 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound397 p)
theorem guard398 (p : Pattern) (guard : pushGuard support p 186 185 184 184 = true) : d829 p = 1 := by
  change (!(p 186) && (!false || false) && !false && (!false || false)) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound398 (p : Pattern) (guard : pushGuard support p 186 185 184 184 = true) : bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder 184 - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some 184)) := by
  have certified := compare4019 p (guard398 p guard)
  change d485 p ≤ (2 : Int) + d258 (change p 185 (some 184))
  have normalized := agree258 _ _ (change_representative support p 185 (some 184) 10000 dummy_outside)
  rw [normalized]
  change d485 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check398 (p : Pattern) : (!pushGuard support p 186 185 184 184 || decide (bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder 184 - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some 184)))) = true :=
  check_of_implication _ _ (bound398 p)
theorem guard399 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 161 .northEast = true) : d1054 p = 1 := by
  change (!(p 186) && !false && !(true && (p 160) && (p 187))) = true at guard
  cases h160 : p 160 <;> cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d829, d851, d1053, d1054, h160, h186, h187] at guard ⊢
theorem bound399 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 161 .northEast = true) : bonus 186 p ≤ bonus 161 p := by
  have certified := compare4104 p (guard399 p guard)
  simpa only [at186, at161, Int.zero_add] using certified
theorem check399 (p : Pattern) : (!walkGuard soko1_2.board support p 186 161 .northEast || decide (bonus 186 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound399 p)
theorem guard400 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 159 .northWest = true) : d1015 p = 1 := by
  change (!(p 186) && !(p 159) && !(true && (p 160) && false)) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d829, d1015, h159, h160, h186] at guard ⊢
theorem bound400 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 159 .northWest = true) : bonus 186 p ≤ bonus 159 p := by
  have certified := compare4145 p (guard400 p guard)
  simpa only [at186, at159, Int.zero_add] using certified
theorem check400 (p : Pattern) : (!walkGuard soko1_2.board support p 186 159 .northWest || decide (bonus 186 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound400 p)
theorem guard401 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 213 .southEast = true) : d829 p = 1 := by
  change (!(p 186) && !false && !(true && false && (p 187))) = true at guard
  cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d829, h186, h187] at guard ⊢
theorem bound401 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 213 .southEast = true) : bonus 186 p ≤ bonus 213 p := by
  have certified := compare3961 p (guard401 p guard)
  simpa only [at186, at213, Int.zero_add] using certified
theorem check401 (p : Pattern) : (!walkGuard soko1_2.board support p 186 213 .southEast || decide (bonus 186 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound401 p)
theorem guard402 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 211 .southWest = true) : d829 p = 1 := by
  change (!(p 186) && !false && !(true && false && false)) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound402 (p : Pattern) (guard : walkGuard soko1_2.board support p 186 211 .southWest = true) : bonus 186 p ≤ bonus 211 p := by
  have certified := compare3961 p (guard402 p guard)
  simpa only [at186, at211, Int.zero_add] using certified
theorem check402 (p : Pattern) : (!walkGuard soko1_2.board support p 186 211 .southWest || decide (bonus 186 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound402 p)
theorem guard403 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 161 .north = true) : d851 p = 1 := by
  change (!(p 187) && !false && !false) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound403 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 161 .north = true) : bonus 187 p ≤ bonus 161 p := by
  have certified := compare4172 p (guard403 p guard)
  simpa only [at187, at161, Int.zero_add] using certified
theorem check403 (p : Pattern) : (!walkGuard soko1_2.board support p 187 161 .north || decide (bonus 187 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound403 p)
theorem guard404 (p : Pattern) (guard : pushGuard support p 187 161 135 135 = true) : d851 p = 1 := by
  change (!(p 187) && (!false || false) && !false && (!false || false)) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound404 (p : Pattern) (guard : pushGuard support p 187 161 135 135 = true) : bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder 135 - Generated.soko1_2Potential.boulder 161 + bonus 161 (change p 161 (some 135)) := by
  have certified := compare4209 p (guard404 p guard)
  change d524 p ≤ (8 : Int) + d236 (change p 161 (some 135))
  have normalized := agree236 _ _ (change_representative support p 161 (some 135) 10000 dummy_outside)
  rw [normalized]
  change d524 p ≤ (8 : Int) + d236 (change p 10000 none)
  rw [sub2066]
  exact certified
theorem check404 (p : Pattern) : (!pushGuard support p 187 161 135 135 || decide (bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder 135 - Generated.soko1_2Potential.boulder 161 + bonus 161 (change p 161 (some 135)))) = true :=
  check_of_implication _ _ (bound404 p)
theorem guard405 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 213 .south = true) : d851 p = 1 := by
  change (!(p 187) && !false && !false) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound405 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 213 .south = true) : bonus 187 p ≤ bonus 213 p := by
  have certified := compare4255 p (guard405 p guard)
  simpa only [at187, at213, Int.zero_add] using certified
theorem check405 (p : Pattern) : (!walkGuard soko1_2.board support p 187 213 .south || decide (bonus 187 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound405 p)
theorem guard406 (p : Pattern) (guard : pushGuard support p 187 213 239 239 = true) : d851 p = 1 := by
  change (!(p 187) && (!false || false) && !false && (!false || false)) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound406 (p : Pattern) (guard : pushGuard support p 187 213 239 239 = true) : bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder 239 - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some 239)) := by
  have certified := compare4319 p (guard406 p guard)
  change d524 p ≤ (2 : Int) + d258 (change p 213 (some 239))
  have normalized := agree258 _ _ (change_representative support p 213 (some 239) 10000 dummy_outside)
  rw [normalized]
  change d524 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check406 (p : Pattern) : (!pushGuard support p 187 213 239 239 || decide (bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder 239 - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some 239)))) = true :=
  check_of_implication _ _ (bound406 p)
theorem guard407 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 186 .west = true) : d1053 p = 1 := by
  change (!(p 187) && !(p 186) && !false) = true at guard
  cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d851, d1053, h186, h187] at guard ⊢
theorem bound407 (p : Pattern) (guard : walkGuard soko1_2.board support p 187 186 .west = true) : bonus 187 p ≤ bonus 186 p := by
  have certified := compare4359 p (guard407 p guard)
  simpa only [at187, at186, Int.zero_add] using certified
theorem check407 (p : Pattern) : (!walkGuard soko1_2.board support p 187 186 .west || decide (bonus 187 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound407 p)
end NetHack.Sokoban12CostPartition
