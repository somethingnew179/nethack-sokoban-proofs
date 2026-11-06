import NetHack.Sokoban12CostPartition.ActionBounds010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard264 (p : Pattern) (guard : pushGuard support p 142 141 140 140 = true) : d767 p = 1 := by
  change (!false && (!true || (p 141)) && !false && (!false || false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d767, h141] at guard ⊢
theorem bound264 (p : Pattern) (guard : pushGuard support p 142 141 140 140 = true) : bonus 142 p ≤ 1 + Generated.soko1_2Potential.boulder 140 - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some 140)) := by
  have certified := compare1345 p (guard264 p guard)
  change d195 p ≤ (1 : Int) + d309 (change p 141 (some 140))
  have normalized := agree309 _ _ (change_representative support p 141 (some 140) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (1 : Int) + d309 (change p 141 none)
  rw [sub268]
  exact certified
theorem check264 (p : Pattern) : (!pushGuard support p 142 141 140 140 || decide (bonus 142 p ≤ 1 + Generated.soko1_2Potential.boulder 140 - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some 140)))) = true :=
  check_of_implication _ _ (bound264 p)
theorem guard265 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 117 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound265 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 117 .northEast = true) : bonus 142 p ≤ bonus 117 p := by
  have certified := compare245 p (guard265 p guard)
  simpa only [at142, at117, Int.zero_add] using certified
theorem check265 (p : Pattern) : (!walkGuard soko1_2.board support p 142 117 .northEast || decide (bonus 142 p ≤ bonus 117 p)) = true :=
  check_of_implication _ _ (bound265 p)
theorem guard266 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 115 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 141))) = true at guard
  cases h141 : p 141
  all_goals simp [d1, h141] at guard ⊢
theorem bound266 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 115 .northWest = true) : bonus 142 p ≤ bonus 115 p := by
  have certified := compare245 p (guard266 p guard)
  simpa only [at142, at115, Int.zero_add] using certified
theorem check266 (p : Pattern) : (!walkGuard soko1_2.board support p 142 115 .northWest || decide (bonus 142 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound266 p)
theorem guard267 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 169 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 168) && false)) = true at guard
  cases h168 : p 168
  all_goals simp [d1, h168] at guard ⊢
theorem bound267 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 169 .southEast = true) : bonus 142 p ≤ bonus 169 p := by
  have certified := compare245 p (guard267 p guard)
  simpa only [at142, at169, Int.zero_add] using certified
theorem check267 (p : Pattern) : (!walkGuard soko1_2.board support p 142 169 .southEast || decide (bonus 142 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound267 p)
theorem guard268 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 167 .southWest = true) : d986 p = 1 := by
  change (!false && !false && !(true && (p 168) && (p 141))) = true at guard
  cases h141 : p 141 <;> cases h168 : p 168
  all_goals simp [d0, d1, d770, d986, h141, h168] at guard ⊢
theorem bound268 (p : Pattern) (guard : walkGuard soko1_2.board support p 142 167 .southWest = true) : bonus 142 p ≤ bonus 167 p := by
  have certified := compare1389 p (guard268 p guard)
  simpa only [at142, at167, Int.zero_add] using certified
theorem check268 (p : Pattern) : (!walkGuard soko1_2.board support p 142 167 .southWest || decide (bonus 142 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound268 p)
theorem guard269 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 117 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound269 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 117 .north = true) : bonus 143 p ≤ bonus 117 p := by
  have certified := compare245 p (guard269 p guard)
  simpa only [at143, at117, Int.zero_add] using certified
theorem check269 (p : Pattern) : (!walkGuard soko1_2.board support p 143 117 .north || decide (bonus 143 p ≤ bonus 117 p)) = true :=
  check_of_implication _ _ (bound269 p)
theorem guard270 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 169 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound270 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 169 .south = true) : bonus 143 p ≤ bonus 169 p := by
  have certified := compare245 p (guard270 p guard)
  simpa only [at143, at169, Int.zero_add] using certified
theorem check270 (p : Pattern) : (!walkGuard soko1_2.board support p 143 169 .south || decide (bonus 143 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound270 p)
theorem guard271 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 142 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound271 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 142 .west = true) : bonus 143 p ≤ bonus 142 p := by
  have certified := compare245 p (guard271 p guard)
  simpa only [at143, at142, Int.zero_add] using certified
theorem check271 (p : Pattern) : (!walkGuard soko1_2.board support p 143 142 .west || decide (bonus 143 p ≤ bonus 142 p)) = true :=
  check_of_implication _ _ (bound271 p)
theorem guard272 (p : Pattern) (guard : pushGuard support p 143 142 141 141 = true) : d768 p = 1 := by
  change (!false && (!false || false) && !(p 141) && (!(p 141) || false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound272 (p : Pattern) (guard : pushGuard support p 143 142 141 141 = true) : bonus 143 p ≤ 1 + Generated.soko1_2Potential.boulder 141 - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some 141)) := by
  have certified := compare1390 p (guard272 p guard)
  change d195 p ≤ (1 : Int) + d195 (change p 142 (some 141))
  have normalized := agree195 _ _ (change_representative support p 142 (some 141) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (1 : Int) + d195 (change p 10000 (some 141))
  rw [sub1128]
  exact certified
theorem check272 (p : Pattern) : (!pushGuard support p 143 142 141 141 || decide (bonus 143 p ≤ 1 + Generated.soko1_2Potential.boulder 141 - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some 141)))) = true :=
  check_of_implication _ _ (bound272 p)
theorem guard273 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 116 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound273 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 116 .northWest = true) : bonus 143 p ≤ bonus 116 p := by
  have certified := compare245 p (guard273 p guard)
  simpa only [at143, at116, Int.zero_add] using certified
theorem check273 (p : Pattern) : (!walkGuard soko1_2.board support p 143 116 .northWest || decide (bonus 143 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound273 p)
theorem guard274 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 168 .southWest = true) : d770 p = 1 := by
  change (!false && !(p 168) && !(true && false && false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound274 (p : Pattern) (guard : walkGuard soko1_2.board support p 143 168 .southWest = true) : bonus 143 p ≤ bonus 168 p := by
  have certified := compare1343 p (guard274 p guard)
  simpa only [at143, at168, Int.zero_add] using certified
theorem check274 (p : Pattern) : (!walkGuard soko1_2.board support p 143 168 .southWest || decide (bonus 143 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound274 p)
theorem guard275 (p : Pattern) (guard : walkGuard soko1_2.board support p 154 128 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound275 (p : Pattern) (guard : walkGuard soko1_2.board support p 154 128 .north = true) : bonus 154 p ≤ bonus 128 p := by
  have certified := compare0 p (guard275 p guard)
  simpa only [at154, at128, Int.zero_add] using certified
theorem check275 (p : Pattern) : (!walkGuard soko1_2.board support p 154 128 .north || decide (bonus 154 p ≤ bonus 128 p)) = true :=
  check_of_implication _ _ (bound275 p)
theorem guard276 (p : Pattern) (guard : pushGuard support p 154 128 102 102 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound276 (p : Pattern) (guard : pushGuard support p 154 128 102 102 = true) : bonus 154 p ≤ 1 + Generated.soko1_2Potential.boulder 102 - Generated.soko1_2Potential.boulder 128 + bonus 128 (change p 128 (some 102)) := by
  have certified := compare3 p (guard276 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 128 (some 102))
  have normalized := agree75 _ _ (change_representative support p 128 (some 102) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check276 (p : Pattern) : (!pushGuard support p 154 128 102 102 || decide (bonus 154 p ≤ 1 + Generated.soko1_2Potential.boulder 102 - Generated.soko1_2Potential.boulder 128 + bonus 128 (change p 128 (some 102)))) = true :=
  check_of_implication _ _ (bound276 p)
theorem guard277 (p : Pattern) (guard : walkGuard soko1_2.board support p 154 180 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound277 (p : Pattern) (guard : walkGuard soko1_2.board support p 154 180 .south = true) : bonus 154 p ≤ bonus 180 p := by
  have certified := compare0 p (guard277 p guard)
  simpa only [at154, at180, Int.zero_add] using certified
theorem check277 (p : Pattern) : (!walkGuard soko1_2.board support p 154 180 .south || decide (bonus 154 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound277 p)
theorem guard278 (p : Pattern) (guard : pushGuard support p 154 180 206 206 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound278 (p : Pattern) (guard : pushGuard support p 154 180 206 206 = true) : bonus 154 p ≤ 1 + Generated.soko1_2Potential.boulder 206 - Generated.soko1_2Potential.boulder 180 + bonus 180 (change p 180 (some 206)) := by
  have certified := compare3 p (guard278 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 180 (some 206))
  have normalized := agree75 _ _ (change_representative support p 180 (some 206) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check278 (p : Pattern) : (!pushGuard support p 154 180 206 206 || decide (bonus 154 p ≤ 1 + Generated.soko1_2Potential.boulder 206 - Generated.soko1_2Potential.boulder 180 + bonus 180 (change p 180 (some 206)))) = true :=
  check_of_implication _ _ (bound278 p)
theorem guard279 (p : Pattern) (guard : walkGuard soko1_2.board support p 157 131 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound279 (p : Pattern) (guard : walkGuard soko1_2.board support p 157 131 .north = true) : bonus 157 p ≤ bonus 131 p := by
  have certified := compare40 p (guard279 p guard)
  simpa only [at157, at131, Int.zero_add] using certified
theorem check279 (p : Pattern) : (!walkGuard soko1_2.board support p 157 131 .north || decide (bonus 157 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound279 p)
theorem guard280 (p : Pattern) (guard : pushGuard support p 157 131 105 105 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound280 (p : Pattern) (guard : pushGuard support p 157 131 105 105 = true) : bonus 157 p ≤ 1 + Generated.soko1_2Potential.boulder 105 - Generated.soko1_2Potential.boulder 131 + bonus 131 (change p 131 (some 105)) := by
  have certified := compare41 p (guard280 p guard)
  change d161 p ≤ (1 : Int) + d161 (change p 131 (some 105))
  have normalized := agree161 _ _ (change_representative support p 131 (some 105) 10000 dummy_outside)
  rw [normalized]
  change d161 p ≤ (1 : Int) + d161 (change p 10000 none)
  rw [sub121]
  exact certified
theorem check280 (p : Pattern) : (!pushGuard support p 157 131 105 105 || decide (bonus 157 p ≤ 1 + Generated.soko1_2Potential.boulder 105 - Generated.soko1_2Potential.boulder 131 + bonus 131 (change p 131 (some 105)))) = true :=
  check_of_implication _ _ (bound280 p)
theorem guard281 (p : Pattern) (guard : walkGuard soko1_2.board support p 157 158 .east = true) : d742 p = 1 := by
  change (!false && !(p 158) && !false) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d742, h158] at guard ⊢
theorem bound281 (p : Pattern) (guard : walkGuard soko1_2.board support p 157 158 .east = true) : bonus 157 p ≤ bonus 158 p := by
  have certified := compare367 p (guard281 p guard)
  simpa only [at157, at158, Int.zero_add] using certified
theorem check281 (p : Pattern) : (!walkGuard soko1_2.board support p 157 158 .east || decide (bonus 157 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound281 p)
theorem guard282 (p : Pattern) (guard : pushGuard support p 157 158 159 159 = true) : d987 p = 1 := by
  change (!false && (!true || (p 158)) && !(p 159) && (!(p 159) || false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, d987, h158, h159] at guard ⊢
theorem bound282 (p : Pattern) (guard : pushGuard support p 157 158 159 159 = true) : bonus 157 p ≤ 1 + Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some 159)) := by
  have certified := compare1443 p (guard282 p guard)
  change d161 p ≤ (0 : Int) + d319 (change p 158 (some 159))
  have normalized := agree319 _ _ (change_representative support p 158 (some 159) 10000 dummy_outside)
  rw [normalized]
  change d161 p ≤ (0 : Int) + d319 (change p 158 (some 159))
  rw [sub1200]
  exact certified
theorem check282 (p : Pattern) : (!pushGuard support p 157 158 159 159 || decide (bonus 157 p ≤ 1 + Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some 159)))) = true :=
  check_of_implication _ _ (bound282 p)
theorem guard283 (p : Pattern) (guard : walkGuard soko1_2.board support p 157 132 .northEast = true) : d740 p = 1 := by
  change (!false && !(p 132) && !(true && false && (p 158))) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d740, h132, h158] at guard ⊢
theorem bound283 (p : Pattern) (guard : walkGuard soko1_2.board support p 157 132 .northEast = true) : bonus 157 p ≤ bonus 132 p := by
  have certified := compare48 p (guard283 p guard)
  simpa only [at157, at132, Int.zero_add] using certified
theorem check283 (p : Pattern) : (!walkGuard soko1_2.board support p 157 132 .northEast || decide (bonus 157 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound283 p)
theorem guard284 (p : Pattern) (guard : walkGuard soko1_2.board support p 157 184 .southEast = true) : d742 p = 1 := by
  change (!false && !false && !(true && true && (p 158))) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d742, h158] at guard ⊢
theorem bound284 (p : Pattern) (guard : walkGuard soko1_2.board support p 157 184 .southEast = true) : bonus 157 p ≤ bonus 184 p := by
  have certified := compare1461 p (guard284 p guard)
  simpa only [at157, at184, Int.zero_add] using certified
theorem check284 (p : Pattern) : (!walkGuard soko1_2.board support p 157 184 .southEast || decide (bonus 157 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound284 p)
theorem guard285 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 132 .north = true) : d773 p = 1 := by
  change (!(p 158) && !(p 132) && !false) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d742, d773, h132, h158] at guard ⊢
theorem bound285 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 132 .north = true) : bonus 158 p ≤ bonus 132 p := by
  have certified := compare1495 p (guard285 p guard)
  simpa only [at158, at132, Int.zero_add] using certified
theorem check285 (p : Pattern) : (!walkGuard soko1_2.board support p 158 132 .north || decide (bonus 158 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound285 p)
theorem guard286 (p : Pattern) (guard : pushGuard support p 158 132 106 106 = true) : d743 p = 1 := by
  change (!(p 158) && (!true || (p 132)) && !false && (!false || false)) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d742, d743, h132, h158] at guard ⊢
theorem bound286 (p : Pattern) (guard : pushGuard support p 158 132 106 106 = true) : bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder 106 - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some 106)) := by
  have certified := compare1571 p (guard286 p guard)
  change d319 p ≤ (12 : Int) + d201 (change p 132 (some 106))
  have normalized := agree201 _ _ (change_representative support p 132 (some 106) 10000 dummy_outside)
  rw [normalized]
  change d319 p ≤ (12 : Int) + d201 (change p 132 none)
  rw [sub676]
  exact certified
theorem check286 (p : Pattern) : (!pushGuard support p 158 132 106 106 || decide (bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder 106 - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some 106)))) = true :=
  check_of_implication _ _ (bound286 p)
theorem guard287 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 184 .south = true) : d742 p = 1 := by
  change (!(p 158) && !false && !false) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d742, h158] at guard ⊢
theorem bound287 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 184 .south = true) : bonus 158 p ≤ bonus 184 p := by
  have certified := compare1592 p (guard287 p guard)
  simpa only [at158, at184, Int.zero_add] using certified
theorem check287 (p : Pattern) : (!walkGuard soko1_2.board support p 158 184 .south || decide (bonus 158 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound287 p)
end NetHack.Sokoban12CostPartition
