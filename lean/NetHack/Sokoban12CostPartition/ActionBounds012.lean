import NetHack.Sokoban12CostPartition.ActionBounds011
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard288 (p : Pattern) (guard : pushGuard support p 158 184 210 210 = true) : d742 p = 1 := by
  change (!(p 158) && (!false || false) && !false && (!false || false)) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d742, h158] at guard ⊢
theorem bound288 (p : Pattern) (guard : pushGuard support p 158 184 210 210 = true) : bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder 210 - Generated.soko1_2Potential.boulder 184 + bonus 184 (change p 184 (some 210)) := by
  have certified := compare1618 p (guard288 p guard)
  change d319 p ≤ (2 : Int) + d258 (change p 184 (some 210))
  have normalized := agree258 _ _ (change_representative support p 184 (some 210) 10000 dummy_outside)
  rw [normalized]
  change d319 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check288 (p : Pattern) : (!pushGuard support p 158 184 210 210 || decide (bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder 210 - Generated.soko1_2Potential.boulder 184 + bonus 184 (change p 184 (some 210)))) = true :=
  check_of_implication _ _ (bound288 p)
theorem guard289 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 159 .east = true) : d798 p = 1 := by
  change (!(p 158) && !(p 159) && !false) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, d798, h158, h159] at guard ⊢
theorem bound289 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 159 .east = true) : bonus 158 p ≤ bonus 159 p := by
  have certified := compare1650 p (guard289 p guard)
  simpa only [at158, at159, Int.zero_add] using certified
theorem check289 (p : Pattern) : (!walkGuard soko1_2.board support p 158 159 .east || decide (bonus 158 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound289 p)
theorem guard290 (p : Pattern) (guard : pushGuard support p 158 159 160 160 = true) : d1001 p = 1 := by
  change (!(p 158) && (!true || (p 159)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d1000, d1001, h158, h159, h160] at guard ⊢
theorem bound290 (p : Pattern) (guard : pushGuard support p 158 159 160 160 = true) : bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some 160)) := by
  have certified := compare1722 p (guard290 p guard)
  change d319 p ≤ (0 : Int) + d356 (change p 159 (some 160))
  have normalized := agree356 _ _ (change_representative support p 159 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d319 p ≤ (0 : Int) + d356 (change p 159 (some 160))
  rw [sub1284]
  exact certified
theorem check290 (p : Pattern) : (!pushGuard support p 158 159 160 160 || decide (bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some 160)))) = true :=
  check_of_implication _ _ (bound290 p)
theorem guard291 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 157 .west = true) : d742 p = 1 := by
  change (!(p 158) && !false && !false) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d742, h158] at guard ⊢
theorem bound291 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 157 .west = true) : bonus 158 p ≤ bonus 157 p := by
  have certified := compare1731 p (guard291 p guard)
  simpa only [at158, at157, Int.zero_add] using certified
theorem check291 (p : Pattern) : (!walkGuard soko1_2.board support p 158 157 .west || decide (bonus 158 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound291 p)
theorem guard292 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 133 .northEast = true) : d825 p = 1 := by
  change (!(p 158) && !(p 133) && !(true && (p 132) && (p 159))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d742, d794, d798, d821, d824, d825, h132, h133, h158, h159] at guard ⊢
theorem bound292 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 133 .northEast = true) : bonus 158 p ≤ bonus 133 p := by
  have certified := compare1749 p (guard292 p guard)
  simpa only [at158, at133, Int.zero_add] using certified
theorem check292 (p : Pattern) : (!walkGuard soko1_2.board support p 158 133 .northEast || decide (bonus 158 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound292 p)
theorem guard293 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 131 .northWest = true) : d742 p = 1 := by
  change (!(p 158) && !false && !(true && (p 132) && false)) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d742, h132, h158] at guard ⊢
theorem bound293 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 131 .northWest = true) : bonus 158 p ≤ bonus 131 p := by
  have certified := compare1731 p (guard293 p guard)
  simpa only [at158, at131, Int.zero_add] using certified
theorem check293 (p : Pattern) : (!walkGuard soko1_2.board support p 158 131 .northWest || decide (bonus 158 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound293 p)
theorem guard294 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 185 .southEast = true) : d742 p = 1 := by
  change (!(p 158) && !false && !(true && false && (p 159))) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d742, h158, h159] at guard ⊢
theorem bound294 (p : Pattern) (guard : walkGuard soko1_2.board support p 158 185 .southEast = true) : bonus 158 p ≤ bonus 185 p := by
  have certified := compare1592 p (guard294 p guard)
  simpa only [at158, at185, Int.zero_add] using certified
theorem check294 (p : Pattern) : (!walkGuard soko1_2.board support p 158 185 .southEast || decide (bonus 158 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound294 p)
theorem guard295 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 133 .north = true) : d801 p = 1 := by
  change (!(p 159) && !(p 133) && !false) = true at guard
  cases h133 : p 133 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, d801, h133, h159] at guard ⊢
theorem bound295 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 133 .north = true) : bonus 159 p ≤ bonus 133 p := by
  have certified := compare1769 p (guard295 p guard)
  simpa only [at159, at133, Int.zero_add] using certified
theorem check295 (p : Pattern) : (!walkGuard soko1_2.board support p 159 133 .north || decide (bonus 159 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound295 p)
theorem guard296 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 185 .south = true) : d794 p = 1 := by
  change (!(p 159) && !false && !false) = true at guard
  cases h159 : p 159
  all_goals simp [d0, d1, d794, h159] at guard ⊢
theorem bound296 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 185 .south = true) : bonus 159 p ≤ bonus 185 p := by
  have certified := compare1800 p (guard296 p guard)
  simpa only [at159, at185, Int.zero_add] using certified
theorem check296 (p : Pattern) : (!walkGuard soko1_2.board support p 159 185 .south || decide (bonus 159 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound296 p)
theorem guard297 (p : Pattern) (guard : pushGuard support p 159 185 211 211 = true) : d794 p = 1 := by
  change (!(p 159) && (!false || false) && !false && (!false || false)) = true at guard
  cases h159 : p 159
  all_goals simp [d0, d1, d794, h159] at guard ⊢
theorem bound297 (p : Pattern) (guard : pushGuard support p 159 185 211 211 = true) : bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some 211)) := by
  have certified := compare1852 p (guard297 p guard)
  change d356 p ≤ (2 : Int) + d258 (change p 185 (some 211))
  have normalized := agree258 _ _ (change_representative support p 185 (some 211) 10000 dummy_outside)
  rw [normalized]
  change d356 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check297 (p : Pattern) : (!pushGuard support p 159 185 211 211 || decide (bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some 211)))) = true :=
  check_of_implication _ _ (bound297 p)
theorem guard298 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 160 .east = true) : d818 p = 1 := by
  change (!(p 159) && !(p 160) && !false) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d818, h159, h160] at guard ⊢
theorem bound298 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 160 .east = true) : bonus 159 p ≤ bonus 160 p := by
  have certified := compare1880 p (guard298 p guard)
  simpa only [at159, at160, Int.zero_add] using certified
theorem check298 (p : Pattern) : (!walkGuard soko1_2.board support p 159 160 .east || decide (bonus 159 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound298 p)
theorem guard299 (p : Pattern) (guard : pushGuard support p 159 160 161 161 = true) : d1014 p = 1 := by
  change (!(p 159) && (!true || (p 160)) && !false && (!false || false)) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d757, d1014, h159, h160] at guard ⊢
theorem bound299 (p : Pattern) (guard : pushGuard support p 159 160 161 161 = true) : bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder 161 - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some 161)) := by
  have certified := compare1943 p (guard299 p guard)
  change d356 p ≤ (6 : Int) + d374 (change p 160 (some 161))
  have normalized := agree374 _ _ (change_representative support p 160 (some 161) 10000 dummy_outside)
  rw [normalized]
  change d356 p ≤ (6 : Int) + d374 (change p 160 none)
  rw [sub1319]
  exact certified
theorem check299 (p : Pattern) : (!pushGuard support p 159 160 161 161 || decide (bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder 161 - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some 161)))) = true :=
  check_of_implication _ _ (bound299 p)
theorem guard300 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 158 .west = true) : d798 p = 1 := by
  change (!(p 159) && !(p 158) && !false) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, d798, h158, h159] at guard ⊢
theorem bound300 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 158 .west = true) : bonus 159 p ≤ bonus 158 p := by
  have certified := compare1970 p (guard300 p guard)
  simpa only [at159, at158, Int.zero_add] using certified
theorem check300 (p : Pattern) : (!walkGuard soko1_2.board support p 159 158 .west || decide (bonus 159 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound300 p)
theorem guard301 (p : Pattern) (guard : pushGuard support p 159 158 157 157 = true) : d987 p = 1 := by
  change (!(p 159) && (!true || (p 158)) && !false && (!false || false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, d987, h158, h159] at guard ⊢
theorem bound301 (p : Pattern) (guard : pushGuard support p 159 158 157 157 = true) : bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder 157 - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some 157)) := by
  have certified := compare2063 p (guard301 p guard)
  change d356 p ≤ (11 : Int) + d319 (change p 158 (some 157))
  have normalized := agree319 _ _ (change_representative support p 158 (some 157) 10000 dummy_outside)
  rw [normalized]
  change d356 p ≤ (11 : Int) + d319 (change p 158 none)
  rw [sub463]
  exact certified
theorem check301 (p : Pattern) : (!pushGuard support p 159 158 157 157 || decide (bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder 157 - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some 157)))) = true :=
  check_of_implication _ _ (bound301 p)
theorem guard302 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 134 .northEast = true) : d849 p = 1 := by
  change (!(p 159) && !(p 134) && !(true && (p 133) && (p 160))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d794, d818, d845, d848, d849, h133, h134, h159, h160] at guard ⊢
theorem bound302 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 134 .northEast = true) : bonus 159 p ≤ bonus 134 p := by
  have certified := compare2089 p (guard302 p guard)
  simpa only [at159, at134, Int.zero_add] using certified
theorem check302 (p : Pattern) : (!walkGuard soko1_2.board support p 159 134 .northEast || decide (bonus 159 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound302 p)
theorem guard303 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 132 .northWest = true) : d800 p = 1 := by
  change (!(p 159) && !(p 132) && !(true && (p 133) && (p 158))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, d798, d799, d800, h132, h133, h158, h159] at guard ⊢
theorem bound303 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 132 .northWest = true) : bonus 159 p ≤ bonus 132 p := by
  have certified := compare2107 p (guard303 p guard)
  simpa only [at159, at132, Int.zero_add] using certified
theorem check303 (p : Pattern) : (!walkGuard soko1_2.board support p 159 132 .northWest || decide (bonus 159 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound303 p)
theorem guard304 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 186 .southEast = true) : d1015 p = 1 := by
  change (!(p 159) && !(p 186) && !(true && false && (p 160))) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d829, d1015, h159, h160, h186] at guard ⊢
theorem bound304 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 186 .southEast = true) : bonus 159 p ≤ bonus 186 p := by
  have certified := compare2168 p (guard304 p guard)
  simpa only [at159, at186, Int.zero_add] using certified
theorem check304 (p : Pattern) : (!walkGuard soko1_2.board support p 159 186 .southEast || decide (bonus 159 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound304 p)
theorem guard305 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 184 .southWest = true) : d794 p = 1 := by
  change (!(p 159) && !false && !(true && false && (p 158))) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, h158, h159] at guard ⊢
theorem bound305 (p : Pattern) (guard : walkGuard soko1_2.board support p 159 184 .southWest = true) : bonus 159 p ≤ bonus 184 p := by
  have certified := compare1800 p (guard305 p guard)
  simpa only [at159, at184, Int.zero_add] using certified
theorem check305 (p : Pattern) : (!walkGuard soko1_2.board support p 159 184 .southWest || decide (bonus 159 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound305 p)
theorem guard306 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 134 .north = true) : d826 p = 1 := by
  change (!(p 160) && !(p 134) && !false) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d826, h134, h160] at guard ⊢
theorem bound306 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 134 .north = true) : bonus 160 p ≤ bonus 134 p := by
  have certified := compare2185 p (guard306 p guard)
  simpa only [at160, at134, Int.zero_add] using certified
theorem check306 (p : Pattern) : (!walkGuard soko1_2.board support p 160 134 .north || decide (bonus 160 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound306 p)
theorem guard307 (p : Pattern) (guard : pushGuard support p 160 134 108 108 = true) : d760 p = 1 := by
  change (!(p 160) && (!true || (p 134)) && !(p 108) && (!(p 108) || false)) = true at guard
  cases h108 : p 108 <;> cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d759, d760, h108, h134, h160] at guard ⊢
theorem bound307 (p : Pattern) (guard : pushGuard support p 160 134 108 108 = true) : bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder 108 - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some 108)) := by
  have certified := compare2195 p (guard307 p guard)
  change d374 p ≤ (0 : Int) + d74 (change p 134 (some 108))
  have normalized := agree74 _ _ (change_representative support p 134 (some 108) 10000 dummy_outside)
  rw [normalized]
  change d374 p ≤ (0 : Int) + d74 (change p 134 (some 108))
  rw [sub1353]
  exact certified
theorem check307 (p : Pattern) : (!pushGuard support p 160 134 108 108 || decide (bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder 108 - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some 108)))) = true :=
  check_of_implication _ _ (bound307 p)
theorem guard308 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 186 .south = true) : d1016 p = 1 := by
  change (!(p 160) && !(p 186) && !false) = true at guard
  cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d829, d1016, h160, h186] at guard ⊢
theorem bound308 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 186 .south = true) : bonus 160 p ≤ bonus 186 p := by
  have certified := compare2237 p (guard308 p guard)
  simpa only [at160, at186, Int.zero_add] using certified
theorem check308 (p : Pattern) : (!walkGuard soko1_2.board support p 160 186 .south || decide (bonus 160 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound308 p)
theorem guard309 (p : Pattern) (guard : pushGuard support p 160 186 212 212 = true) : d1017 p = 1 := by
  change (!(p 160) && (!true || (p 186)) && !false && (!false || false)) = true at guard
  cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d828, d1017, h160, h186] at guard ⊢
theorem bound309 (p : Pattern) (guard : pushGuard support p 160 186 212 212 = true) : bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some 212)) := by
  have certified := compare2278 p (guard309 p guard)
  change d374 p ≤ (2 : Int) + d485 (change p 186 (some 212))
  have normalized := agree485 _ _ (change_representative support p 186 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d374 p ≤ (2 : Int) + d485 (change p 186 none)
  rw [sub1415]
  exact certified
theorem check309 (p : Pattern) : (!pushGuard support p 160 186 212 212 || decide (bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some 212)))) = true :=
  check_of_implication _ _ (bound309 p)
theorem guard310 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 161 .east = true) : d758 p = 1 := by
  change (!(p 160) && !false && !false) = true at guard
  cases h160 : p 160
  all_goals simp [d0, d1, d758, h160] at guard ⊢
theorem bound310 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 161 .east = true) : bonus 160 p ≤ bonus 161 p := by
  have certified := compare2289 p (guard310 p guard)
  simpa only [at160, at161, Int.zero_add] using certified
theorem check310 (p : Pattern) : (!walkGuard soko1_2.board support p 160 161 .east || decide (bonus 160 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound310 p)
theorem guard311 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 159 .west = true) : d818 p = 1 := by
  change (!(p 160) && !(p 159) && !false) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d818, h159, h160] at guard ⊢
theorem bound311 (p : Pattern) (guard : walkGuard soko1_2.board support p 160 159 .west = true) : bonus 160 p ≤ bonus 159 p := by
  have certified := compare2320 p (guard311 p guard)
  simpa only [at160, at159, Int.zero_add] using certified
theorem check311 (p : Pattern) : (!walkGuard soko1_2.board support p 160 159 .west || decide (bonus 160 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound311 p)
end NetHack.Sokoban12CostPartition
