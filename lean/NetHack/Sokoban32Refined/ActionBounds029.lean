import NetHack.Sokoban32Refined.ActionBounds028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard696 (p : Pattern) (guard : pushGuard support p 161 135 109 109 = true) : d985 p = 1 := by
  change (!(p 161) && (!false || false) && !false && (!false || false)) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound696 (p : Pattern) (guard : pushGuard support p 161 135 109 109 = true) : bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder 109 - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some 109)) := by
  have certified := compare8630 p (guard696 p guard)
  change d825 p ≤ (4 : Int) + d134 (change p 135 (some 109))
  have normalized := agree134 _ _ (change_representative support p 135 (some 109) 10000 dummy_outside)
  rw [normalized]
  change d825 p ≤ (4 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check696 (p : Pattern) : (!pushGuard support p 161 135 109 109 || decide (bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder 109 - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some 109)))) = true :=
  check_of_implication _ _ (bound696 p)
theorem guard697 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 162 .east = true) : d985 p = 1 := by
  change (!(p 161) && !false && !false) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound697 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 162 .east = true) : bonus 161 p ≤ bonus 162 p := by
  have certified := compare8491 p (guard697 p guard)
  simpa only [at161, at162, Int.zero_add] using certified
theorem check697 (p : Pattern) : (!walkGuard soko3_2.board support p 161 162 .east || decide (bonus 161 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound697 p)
theorem guard698 (p : Pattern) (guard : pushGuard support p 161 162 163 163 = true) : d985 p = 1 := by
  change (!(p 161) && (!false || false) && !false && (!false || false)) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound698 (p : Pattern) (guard : pushGuard support p 161 162 163 163 = true) : bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder 163 - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some 163)) := by
  have certified := compare8491 p (guard698 p guard)
  change d825 p ≤ (0 : Int) + d134 (change p 162 (some 163))
  have normalized := agree134 _ _ (change_representative support p 162 (some 163) 10000 dummy_outside)
  rw [normalized]
  change d825 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check698 (p : Pattern) : (!pushGuard support p 161 162 163 163 || decide (bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder 163 - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some 163)))) = true :=
  check_of_implication _ _ (bound698 p)
theorem guard699 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 160 .west = true) : d1293 p = 1 := by
  change (!(p 161) && !(p 160) && !false) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d985, d1293, h160, h161] at guard ⊢
theorem bound699 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 160 .west = true) : bonus 161 p ≤ bonus 160 p := by
  have certified := compare8715 p (guard699 p guard)
  simpa only [at161, at160, Int.zero_add] using certified
theorem check699 (p : Pattern) : (!walkGuard soko3_2.board support p 161 160 .west || decide (bonus 161 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound699 p)
theorem guard700 (p : Pattern) (guard : pushGuard support p 161 160 159 159 = true) : d1553 p = 1 := by
  change (!(p 161) && (!true || (p 160)) && !(p 159) && (!(p 159) || false)) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d985, d1552, d1553, h159, h160, h161] at guard ⊢
theorem bound700 (p : Pattern) (guard : pushGuard support p 161 160 159 159 = true) : bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder 159 - Generated.soko3_2Potential.boulder 160 + bonus 160 (change p 160 (some 159)) := by
  have certified := compare8820 p (guard700 p guard)
  change d825 p ≤ (2 : Int) + d742 (change p 160 (some 159))
  have normalized := agree742 _ _ (change_representative support p 160 (some 159) 10000 dummy_outside)
  rw [normalized]
  change d825 p ≤ (2 : Int) + d742 (change p 160 (some 159))
  rw [sub3231]
  exact certified
theorem check700 (p : Pattern) : (!pushGuard support p 161 160 159 159 || decide (bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder 159 - Generated.soko3_2Potential.boulder 160 + bonus 160 (change p 160 (some 159)))) = true :=
  check_of_implication _ _ (bound700 p)
theorem guard701 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 136 .northEast = true) : d985 p = 1 := by
  change (!(p 161) && !false && !(true && false && false)) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound701 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 136 .northEast = true) : bonus 161 p ≤ bonus 136 p := by
  have certified := compare8491 p (guard701 p guard)
  simpa only [at161, at136, Int.zero_add] using certified
theorem check701 (p : Pattern) : (!walkGuard soko3_2.board support p 161 136 .northEast || decide (bonus 161 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound701 p)
theorem guard702 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 134 .northWest = true) : d1249 p = 1 := by
  change (!(p 161) && !(p 134) && !(true && false && (p 160))) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d985, d1249, h134, h160, h161] at guard ⊢
theorem bound702 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 134 .northWest = true) : bonus 161 p ≤ bonus 134 p := by
  have certified := compare8905 p (guard702 p guard)
  simpa only [at161, at134, Int.zero_add] using certified
theorem check702 (p : Pattern) : (!walkGuard soko3_2.board support p 161 134 .northWest || decide (bonus 161 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound702 p)
theorem guard703 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 188 .southEast = true) : d985 p = 1 := by
  change (!(p 161) && !false && !(true && true && false)) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound703 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 188 .southEast = true) : bonus 161 p ≤ bonus 188 p := by
  have certified := compare8491 p (guard703 p guard)
  simpa only [at161, at188, Int.zero_add] using certified
theorem check703 (p : Pattern) : (!walkGuard soko3_2.board support p 161 188 .southEast || decide (bonus 161 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound703 p)
theorem guard704 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 136 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound704 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 136 .north = true) : bonus 162 p ≤ bonus 136 p := by
  have certified := compare0 p (guard704 p guard)
  simpa only [at162, at136, Int.zero_add] using certified
theorem check704 (p : Pattern) : (!walkGuard soko3_2.board support p 162 136 .north || decide (bonus 162 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound704 p)
theorem guard705 (p : Pattern) (guard : pushGuard support p 162 136 110 110 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound705 (p : Pattern) (guard : pushGuard support p 162 136 110 110 = true) : bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder 110 - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some 110)) := by
  have certified := compare8906 p (guard705 p guard)
  change d134 p ≤ (5 : Int) + d134 (change p 136 (some 110))
  have normalized := agree134 _ _ (change_representative support p 136 (some 110) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (5 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check705 (p : Pattern) : (!pushGuard support p 162 136 110 110 || decide (bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder 110 - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some 110)))) = true :=
  check_of_implication _ _ (bound705 p)
theorem guard706 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 188 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound706 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 188 .south = true) : bonus 162 p ≤ bonus 188 p := by
  have certified := compare0 p (guard706 p guard)
  simpa only [at162, at188, Int.zero_add] using certified
theorem check706 (p : Pattern) : (!walkGuard soko3_2.board support p 162 188 .south || decide (bonus 162 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound706 p)
theorem guard707 (p : Pattern) (guard : pushGuard support p 162 188 214 214 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound707 (p : Pattern) (guard : pushGuard support p 162 188 214 214 = true) : bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder 214 - Generated.soko3_2Potential.boulder 188 + bonus 188 (change p 188 (some 214)) := by
  have certified := compare0 p (guard707 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 188 (some 214))
  have normalized := agree134 _ _ (change_representative support p 188 (some 214) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check707 (p : Pattern) : (!pushGuard support p 162 188 214 214 || decide (bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder 214 - Generated.soko3_2Potential.boulder 188 + bonus 188 (change p 188 (some 214)))) = true :=
  check_of_implication _ _ (bound707 p)
theorem guard708 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 163 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound708 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 163 .east = true) : bonus 162 p ≤ bonus 163 p := by
  have certified := compare0 p (guard708 p guard)
  simpa only [at162, at163, Int.zero_add] using certified
theorem check708 (p : Pattern) : (!walkGuard soko3_2.board support p 162 163 .east || decide (bonus 162 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound708 p)
theorem guard709 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 161 .west = true) : d985 p = 1 := by
  change (!false && !(p 161) && !false) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound709 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 161 .west = true) : bonus 162 p ≤ bonus 161 p := by
  have certified := compare4300 p (guard709 p guard)
  simpa only [at162, at161, Int.zero_add] using certified
theorem check709 (p : Pattern) : (!walkGuard soko3_2.board support p 162 161 .west || decide (bonus 162 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound709 p)
theorem guard710 (p : Pattern) (guard : pushGuard support p 162 161 160 160 = true) : d1690 p = 1 := by
  change (!false && (!true || (p 161)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d29, d1690, h160, h161] at guard ⊢
theorem bound710 (p : Pattern) (guard : pushGuard support p 162 161 160 160 = true) : bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder 160 - Generated.soko3_2Potential.boulder 161 + bonus 161 (change p 161 (some 160)) := by
  have certified := compare9045 p (guard710 p guard)
  change d134 p ≤ (2 : Int) + d825 (change p 161 (some 160))
  have normalized := agree825 _ _ (change_representative support p 161 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d825 (change p 161 (some 160))
  rw [sub3323]
  exact certified
theorem check710 (p : Pattern) : (!pushGuard support p 162 161 160 160 || decide (bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder 160 - Generated.soko3_2Potential.boulder 161 + bonus 161 (change p 161 (some 160)))) = true :=
  check_of_implication _ _ (bound710 p)
theorem guard711 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 137 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound711 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 137 .northEast = true) : bonus 162 p ≤ bonus 137 p := by
  have certified := compare0 p (guard711 p guard)
  simpa only [at162, at137, Int.zero_add] using certified
theorem check711 (p : Pattern) : (!walkGuard soko3_2.board support p 162 137 .northEast || decide (bonus 162 p ≤ bonus 137 p)) = true :=
  check_of_implication _ _ (bound711 p)
theorem guard712 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 135 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 161))) = true at guard
  cases h161 : p 161
  all_goals simp [d1, h161] at guard ⊢
theorem bound712 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 135 .northWest = true) : bonus 162 p ≤ bonus 135 p := by
  have certified := compare0 p (guard712 p guard)
  simpa only [at162, at135, Int.zero_add] using certified
theorem check712 (p : Pattern) : (!walkGuard soko3_2.board support p 162 135 .northWest || decide (bonus 162 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound712 p)
theorem guard713 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 189 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound713 (p : Pattern) (guard : walkGuard soko3_2.board support p 162 189 .southEast = true) : bonus 162 p ≤ bonus 189 p := by
  have certified := compare0 p (guard713 p guard)
  simpa only [at162, at189, Int.zero_add] using certified
theorem check713 (p : Pattern) : (!walkGuard soko3_2.board support p 162 189 .southEast || decide (bonus 162 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound713 p)
theorem guard714 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 137 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound714 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 137 .north = true) : bonus 163 p ≤ bonus 137 p := by
  have certified := compare0 p (guard714 p guard)
  simpa only [at163, at137, Int.zero_add] using certified
theorem check714 (p : Pattern) : (!walkGuard soko3_2.board support p 163 137 .north || decide (bonus 163 p ≤ bonus 137 p)) = true :=
  check_of_implication _ _ (bound714 p)
theorem guard715 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 189 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound715 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 189 .south = true) : bonus 163 p ≤ bonus 189 p := by
  have certified := compare0 p (guard715 p guard)
  simpa only [at163, at189, Int.zero_add] using certified
theorem check715 (p : Pattern) : (!walkGuard soko3_2.board support p 163 189 .south || decide (bonus 163 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound715 p)
theorem guard716 (p : Pattern) (guard : pushGuard support p 163 189 215 215 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound716 (p : Pattern) (guard : pushGuard support p 163 189 215 215 = true) : bonus 163 p ≤ 1 + Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.boulder 189 + bonus 189 (change p 189 (some 215)) := by
  have certified := compare0 p (guard716 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 189 (some 215))
  have normalized := agree134 _ _ (change_representative support p 189 (some 215) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check716 (p : Pattern) : (!pushGuard support p 163 189 215 215 || decide (bonus 163 p ≤ 1 + Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.boulder 189 + bonus 189 (change p 189 (some 215)))) = true :=
  check_of_implication _ _ (bound716 p)
theorem guard717 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 162 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound717 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 162 .west = true) : bonus 163 p ≤ bonus 162 p := by
  have certified := compare0 p (guard717 p guard)
  simpa only [at163, at162, Int.zero_add] using certified
theorem check717 (p : Pattern) : (!walkGuard soko3_2.board support p 163 162 .west || decide (bonus 163 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound717 p)
theorem guard718 (p : Pattern) (guard : pushGuard support p 163 162 161 161 = true) : d985 p = 1 := by
  change (!false && (!false || false) && !(p 161) && (!(p 161) || false)) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound718 (p : Pattern) (guard : pushGuard support p 163 162 161 161 = true) : bonus 163 p ≤ 1 + Generated.soko3_2Potential.boulder 161 - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some 161)) := by
  have certified := compare9178 p (guard718 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 162 (some 161))
  have normalized := agree134 _ _ (change_representative support p 162 (some 161) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 (some 161))
  rw [sub1031]
  exact certified
theorem check718 (p : Pattern) : (!pushGuard support p 163 162 161 161 || decide (bonus 163 p ≤ 1 + Generated.soko3_2Potential.boulder 161 - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some 161)))) = true :=
  check_of_implication _ _ (bound718 p)
theorem guard719 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 138 .northEast = true) : d857 p = 1 := by
  change (!false && !(p 138) && !(true && false && true)) = true at guard
  cases h138 : p 138
  all_goals simp [d0, d1, d857, h138] at guard ⊢
theorem bound719 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 138 .northEast = true) : bonus 163 p ≤ bonus 138 p := by
  have certified := compare4964 p (guard719 p guard)
  simpa only [at163, at138, Int.zero_add] using certified
theorem check719 (p : Pattern) : (!walkGuard soko3_2.board support p 163 138 .northEast || decide (bonus 163 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound719 p)
end NetHack.Sokoban32Refined
