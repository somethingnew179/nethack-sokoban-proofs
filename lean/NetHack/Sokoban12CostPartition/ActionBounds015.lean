import NetHack.Sokoban12CostPartition.ActionBounds014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard360 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 141 .northWest = true) : d984 p = 1 := by
  change (!(p 168) && !(p 141) && !(true && false && false)) = true at guard
  cases h141 : p 141 <;> cases h168 : p 168
  all_goals simp [d0, d1, d770, d984, h141, h168] at guard ⊢
theorem bound360 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 141 .northWest = true) : bonus 168 p ≤ bonus 141 p := by
  have certified := compare3345 p (guard360 p guard)
  simpa only [at168, at141, Int.zero_add] using certified
theorem check360 (p : Pattern) : (!walkGuard soko1_2.board support p 168 141 .northWest || decide (bonus 168 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound360 p)
theorem guard361 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 193 .southWest = true) : d1134 p = 1 := by
  change (!(p 168) && !(p 193) && !(true && false && false)) = true at guard
  cases h168 : p 168 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d1134, h168, h193] at guard ⊢
theorem bound361 (p : Pattern) (guard : walkGuard soko1_2.board support p 168 193 .southWest = true) : bonus 168 p ≤ bonus 193 p := by
  have certified := compare3413 p (guard361 p guard)
  simpa only [at168, at193, Int.zero_add] using certified
theorem check361 (p : Pattern) : (!walkGuard soko1_2.board support p 168 193 .southWest || decide (bonus 168 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound361 p)
theorem guard362 (p : Pattern) (guard : walkGuard soko1_2.board support p 169 143 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound362 (p : Pattern) (guard : walkGuard soko1_2.board support p 169 143 .north = true) : bonus 169 p ≤ bonus 143 p := by
  have certified := compare245 p (guard362 p guard)
  simpa only [at169, at143, Int.zero_add] using certified
theorem check362 (p : Pattern) : (!walkGuard soko1_2.board support p 169 143 .north || decide (bonus 169 p ≤ bonus 143 p)) = true :=
  check_of_implication _ _ (bound362 p)
theorem guard363 (p : Pattern) (guard : pushGuard support p 169 143 117 117 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound363 (p : Pattern) (guard : pushGuard support p 169 143 117 117 = true) : bonus 169 p ≤ 1 + Generated.soko1_2Potential.boulder 117 - Generated.soko1_2Potential.boulder 143 + bonus 143 (change p 143 (some 117)) := by
  have certified := compare246 p (guard363 p guard)
  change d195 p ≤ (1 : Int) + d195 (change p 143 (some 117))
  have normalized := agree195 _ _ (change_representative support p 143 (some 117) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (1 : Int) + d195 (change p 10000 none)
  rw [sub285]
  exact certified
theorem check363 (p : Pattern) : (!pushGuard support p 169 143 117 117 || decide (bonus 169 p ≤ 1 + Generated.soko1_2Potential.boulder 117 - Generated.soko1_2Potential.boulder 143 + bonus 143 (change p 143 (some 117)))) = true :=
  check_of_implication _ _ (bound363 p)
theorem guard364 (p : Pattern) (guard : walkGuard soko1_2.board support p 169 168 .west = true) : d770 p = 1 := by
  change (!false && !(p 168) && !false) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound364 (p : Pattern) (guard : walkGuard soko1_2.board support p 169 168 .west = true) : bonus 169 p ≤ bonus 168 p := by
  have certified := compare1343 p (guard364 p guard)
  simpa only [at169, at168, Int.zero_add] using certified
theorem check364 (p : Pattern) : (!walkGuard soko1_2.board support p 169 168 .west || decide (bonus 169 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound364 p)
theorem guard365 (p : Pattern) (guard : pushGuard support p 169 168 167 167 = true) : d769 p = 1 := by
  change (!false && (!true || (p 168)) && !false && (!false || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d769, h168] at guard ⊢
theorem bound365 (p : Pattern) (guard : pushGuard support p 169 168 167 167 = true) : bonus 169 p ≤ 1 + Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some 167)) := by
  have certified := compare3414 p (guard365 p guard)
  change d195 p ≤ (0 : Int) + d430 (change p 168 (some 167))
  have normalized := agree430 _ _ (change_representative support p 168 (some 167) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (0 : Int) + d430 (change p 168 none)
  rw [sub1091]
  exact certified
theorem check365 (p : Pattern) : (!pushGuard support p 169 168 167 167 || decide (bonus 169 p ≤ 1 + Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some 167)))) = true :=
  check_of_implication _ _ (bound365 p)
theorem guard366 (p : Pattern) (guard : walkGuard soko1_2.board support p 169 142 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 168))) = true at guard
  cases h168 : p 168
  all_goals simp [d1, h168] at guard ⊢
theorem bound366 (p : Pattern) (guard : walkGuard soko1_2.board support p 169 142 .northWest = true) : bonus 169 p ≤ bonus 142 p := by
  have certified := compare245 p (guard366 p guard)
  simpa only [at169, at142, Int.zero_add] using certified
theorem check366 (p : Pattern) : (!walkGuard soko1_2.board support p 169 142 .northWest || decide (bonus 169 p ≤ bonus 142 p)) = true :=
  check_of_implication _ _ (bound366 p)
theorem guard367 (p : Pattern) (guard : walkGuard soko1_2.board support p 169 194 .southWest = true) : d770 p = 1 := by
  change (!false && !false && !(true && true && (p 168))) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound367 (p : Pattern) (guard : walkGuard soko1_2.board support p 169 194 .southWest = true) : bonus 169 p ≤ bonus 194 p := by
  have certified := compare3442 p (guard367 p guard)
  simpa only [at169, at194, Int.zero_add] using certified
theorem check367 (p : Pattern) : (!walkGuard soko1_2.board support p 169 194 .southWest || decide (bonus 169 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound367 p)
theorem guard368 (p : Pattern) (guard : walkGuard soko1_2.board support p 180 154 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound368 (p : Pattern) (guard : walkGuard soko1_2.board support p 180 154 .north = true) : bonus 180 p ≤ bonus 154 p := by
  have certified := compare0 p (guard368 p guard)
  simpa only [at180, at154, Int.zero_add] using certified
theorem check368 (p : Pattern) : (!walkGuard soko1_2.board support p 180 154 .north || decide (bonus 180 p ≤ bonus 154 p)) = true :=
  check_of_implication _ _ (bound368 p)
theorem guard369 (p : Pattern) (guard : pushGuard support p 180 154 128 128 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound369 (p : Pattern) (guard : pushGuard support p 180 154 128 128 = true) : bonus 180 p ≤ 1 + Generated.soko1_2Potential.boulder 128 - Generated.soko1_2Potential.boulder 154 + bonus 154 (change p 154 (some 128)) := by
  have certified := compare3 p (guard369 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 154 (some 128))
  have normalized := agree75 _ _ (change_representative support p 154 (some 128) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check369 (p : Pattern) : (!pushGuard support p 180 154 128 128 || decide (bonus 180 p ≤ 1 + Generated.soko1_2Potential.boulder 128 - Generated.soko1_2Potential.boulder 154 + bonus 154 (change p 154 (some 128)))) = true :=
  check_of_implication _ _ (bound369 p)
theorem guard370 (p : Pattern) (guard : walkGuard soko1_2.board support p 180 206 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound370 (p : Pattern) (guard : walkGuard soko1_2.board support p 180 206 .south = true) : bonus 180 p ≤ bonus 206 p := by
  have certified := compare0 p (guard370 p guard)
  simpa only [at180, at206, Int.zero_add] using certified
theorem check370 (p : Pattern) : (!walkGuard soko1_2.board support p 180 206 .south || decide (bonus 180 p ≤ bonus 206 p)) = true :=
  check_of_implication _ _ (bound370 p)
theorem guard371 (p : Pattern) (guard : pushGuard support p 180 206 232 232 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound371 (p : Pattern) (guard : pushGuard support p 180 206 232 232 = true) : bonus 180 p ≤ 1 + Generated.soko1_2Potential.boulder 232 - Generated.soko1_2Potential.boulder 206 + bonus 206 (change p 206 (some 232)) := by
  have certified := compare3 p (guard371 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 206 (some 232))
  have normalized := agree75 _ _ (change_representative support p 206 (some 232) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check371 (p : Pattern) : (!pushGuard support p 180 206 232 232 || decide (bonus 180 p ≤ 1 + Generated.soko1_2Potential.boulder 232 - Generated.soko1_2Potential.boulder 206 + bonus 206 (change p 206 (some 232)))) = true :=
  check_of_implication _ _ (bound371 p)
theorem guard372 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 158 .north = true) : d742 p = 1 := by
  change (!false && !(p 158) && !false) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d742, h158] at guard ⊢
theorem bound372 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 158 .north = true) : bonus 184 p ≤ bonus 158 p := by
  have certified := compare3459 p (guard372 p guard)
  simpa only [at184, at158, Int.zero_add] using certified
theorem check372 (p : Pattern) : (!walkGuard soko1_2.board support p 184 158 .north || decide (bonus 184 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound372 p)
theorem guard373 (p : Pattern) (guard : pushGuard support p 184 158 132 132 = true) : d774 p = 1 := by
  change (!false && (!true || (p 158)) && !(p 132) && (!(p 132) || false)) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d741, d774, h132, h158] at guard ⊢
theorem bound373 (p : Pattern) (guard : pushGuard support p 184 158 132 132 = true) : bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder 132 - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some 132)) := by
  have certified := compare3491 p (guard373 p guard)
  change d258 p ≤ (0 : Int) + d319 (change p 158 (some 132))
  have normalized := agree319 _ _ (change_representative support p 158 (some 132) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d319 (change p 158 (some 132))
  rw [sub1823]
  exact certified
theorem check373 (p : Pattern) : (!pushGuard support p 184 158 132 132 || decide (bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder 132 - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some 132)))) = true :=
  check_of_implication _ _ (bound373 p)
theorem guard374 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 210 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound374 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 210 .south = true) : bonus 184 p ≤ bonus 210 p := by
  have certified := compare897 p (guard374 p guard)
  simpa only [at184, at210, Int.zero_add] using certified
theorem check374 (p : Pattern) : (!walkGuard soko1_2.board support p 184 210 .south || decide (bonus 184 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound374 p)
theorem guard375 (p : Pattern) (guard : pushGuard support p 184 210 236 236 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound375 (p : Pattern) (guard : pushGuard support p 184 210 236 236 = true) : bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder 236 - Generated.soko1_2Potential.boulder 210 + bonus 210 (change p 210 (some 236)) := by
  have certified := compare2570 p (guard375 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 210 (some 236))
  have normalized := agree258 _ _ (change_representative support p 210 (some 236) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check375 (p : Pattern) : (!pushGuard support p 184 210 236 236 || decide (bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder 236 - Generated.soko1_2Potential.boulder 210 + bonus 210 (change p 210 (some 236)))) = true :=
  check_of_implication _ _ (bound375 p)
theorem guard376 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 185 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound376 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 185 .east = true) : bonus 184 p ≤ bonus 185 p := by
  have certified := compare897 p (guard376 p guard)
  simpa only [at184, at185, Int.zero_add] using certified
theorem check376 (p : Pattern) : (!walkGuard soko1_2.board support p 184 185 .east || decide (bonus 184 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound376 p)
theorem guard377 (p : Pattern) (guard : pushGuard support p 184 185 186 186 = true) : d829 p = 1 := by
  change (!false && (!false || false) && !(p 186) && (!(p 186) || false)) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound377 (p : Pattern) (guard : pushGuard support p 184 185 186 186 = true) : bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some 186)) := by
  have certified := compare3550 p (guard377 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 185 (some 186))
  have normalized := agree258 _ _ (change_representative support p 185 (some 186) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 (some 186))
  rw [sub1901]
  exact certified
theorem check377 (p : Pattern) : (!pushGuard support p 184 185 186 186 || decide (bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some 186)))) = true :=
  check_of_implication _ _ (bound377 p)
theorem guard378 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 159 .northEast = true) : d794 p = 1 := by
  change (!false && !(p 159) && !(true && (p 158) && false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, h158, h159] at guard ⊢
theorem bound378 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 159 .northEast = true) : bonus 184 p ≤ bonus 159 p := by
  have certified := compare3577 p (guard378 p guard)
  simpa only [at184, at159, Int.zero_add] using certified
theorem check378 (p : Pattern) : (!walkGuard soko1_2.board support p 184 159 .northEast || decide (bonus 184 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound378 p)
theorem guard379 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 157 .northWest = true) : d742 p = 1 := by
  change (!false && !false && !(true && (p 158) && true)) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d742, h158] at guard ⊢
theorem bound379 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 157 .northWest = true) : bonus 184 p ≤ bonus 157 p := by
  have certified := compare3594 p (guard379 p guard)
  simpa only [at184, at157, Int.zero_add] using certified
theorem check379 (p : Pattern) : (!walkGuard soko1_2.board support p 184 157 .northWest || decide (bonus 184 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound379 p)
theorem guard380 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 211 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound380 (p : Pattern) (guard : walkGuard soko1_2.board support p 184 211 .southEast = true) : bonus 184 p ≤ bonus 211 p := by
  have certified := compare897 p (guard380 p guard)
  simpa only [at184, at211, Int.zero_add] using certified
theorem check380 (p : Pattern) : (!walkGuard soko1_2.board support p 184 211 .southEast || decide (bonus 184 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound380 p)
theorem guard381 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 159 .north = true) : d794 p = 1 := by
  change (!false && !(p 159) && !false) = true at guard
  cases h159 : p 159
  all_goals simp [d0, d1, d794, h159] at guard ⊢
theorem bound381 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 159 .north = true) : bonus 185 p ≤ bonus 159 p := by
  have certified := compare3577 p (guard381 p guard)
  simpa only [at185, at159, Int.zero_add] using certified
theorem check381 (p : Pattern) : (!walkGuard soko1_2.board support p 185 159 .north || decide (bonus 185 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound381 p)
theorem guard382 (p : Pattern) (guard : pushGuard support p 185 159 133 133 = true) : d802 p = 1 := by
  change (!false && (!true || (p 159)) && !(p 133) && (!(p 133) || false)) = true at guard
  cases h133 : p 133 <;> cases h159 : p 159
  all_goals simp [d0, d1, d793, d802, h133, h159] at guard ⊢
theorem bound382 (p : Pattern) (guard : pushGuard support p 185 159 133 133 = true) : bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some 133)) := by
  have certified := compare3646 p (guard382 p guard)
  change d258 p ≤ (0 : Int) + d356 (change p 159 (some 133))
  have normalized := agree356 _ _ (change_representative support p 159 (some 133) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d356 (change p 159 (some 133))
  rw [sub1959]
  exact certified
theorem check382 (p : Pattern) : (!pushGuard support p 185 159 133 133 || decide (bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some 133)))) = true :=
  check_of_implication _ _ (bound382 p)
theorem guard383 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 211 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound383 (p : Pattern) (guard : walkGuard soko1_2.board support p 185 211 .south = true) : bonus 185 p ≤ bonus 211 p := by
  have certified := compare897 p (guard383 p guard)
  simpa only [at185, at211, Int.zero_add] using certified
theorem check383 (p : Pattern) : (!walkGuard soko1_2.board support p 185 211 .south || decide (bonus 185 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound383 p)
end NetHack.Sokoban12CostPartition
