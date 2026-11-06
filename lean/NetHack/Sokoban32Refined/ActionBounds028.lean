import NetHack.Sokoban32Refined.ActionBounds027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard672 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 132 .north = true) : d1148 p = 1 := by
  change (!(p 158) && !(p 132) && !false) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d873, d1148, h132, h158] at guard ⊢
theorem bound672 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 132 .north = true) : bonus 158 p ≤ bonus 132 p := by
  have certified := compare6491 p (guard672 p guard)
  simpa only [at158, at132, Int.zero_add] using certified
theorem check672 (p : Pattern) : (!walkGuard soko3_2.board support p 158 132 .north || decide (bonus 158 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound672 p)
theorem guard673 (p : Pattern) (guard : pushGuard support p 158 132 106 106 = true) : d875 p = 1 := by
  change (!(p 158) && (!true || (p 132)) && !(p 106) && (!(p 106) || false)) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d873, d874, d875, h106, h132, h158] at guard ⊢
theorem bound673 (p : Pattern) (guard : pushGuard support p 158 132 106 106 = true) : bonus 158 p ≤ 1 + Generated.soko3_2Potential.boulder 106 - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some 106)) := by
  have certified := compare6621 p (guard673 p guard)
  change d652 p ≤ (1 : Int) + d292 (change p 132 (some 106))
  have normalized := agree292 _ _ (change_representative support p 132 (some 106) 10000 dummy_outside)
  rw [normalized]
  change d652 p ≤ (1 : Int) + d292 (change p 132 (some 106))
  rw [sub2794]
  exact certified
theorem check673 (p : Pattern) : (!pushGuard support p 158 132 106 106 || decide (bonus 158 p ≤ 1 + Generated.soko3_2Potential.boulder 106 - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some 106)))) = true :=
  check_of_implication _ _ (bound673 p)
theorem guard674 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 159 .east = true) : d1171 p = 1 := by
  change (!(p 158) && !(p 159) && !false) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d1167, d1171, h158, h159] at guard ⊢
theorem bound674 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 159 .east = true) : bonus 158 p ≤ bonus 159 p := by
  have certified := compare6738 p (guard674 p guard)
  simpa only [at158, at159, Int.zero_add] using certified
theorem check674 (p : Pattern) : (!walkGuard soko3_2.board support p 158 159 .east || decide (bonus 158 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound674 p)
theorem guard675 (p : Pattern) (guard : pushGuard support p 158 159 160 160 = true) : d1506 p = 1 := by
  change (!(p 158) && (!true || (p 159)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1505, d1506, h158, h159, h160] at guard ⊢
theorem bound675 (p : Pattern) (guard : pushGuard support p 158 159 160 160 = true) : bonus 158 p ≤ 1 + Generated.soko3_2Potential.boulder 160 - Generated.soko3_2Potential.boulder 159 + bonus 159 (change p 159 (some 160)) := by
  have certified := compare6864 p (guard675 p guard)
  change d652 p ≤ (0 : Int) + d696 (change p 159 (some 160))
  have normalized := agree696 _ _ (change_representative support p 159 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d652 p ≤ (0 : Int) + d696 (change p 159 (some 160))
  rw [sub2847]
  exact certified
theorem check675 (p : Pattern) : (!pushGuard support p 158 159 160 160 || decide (bonus 158 p ≤ 1 + Generated.soko3_2Potential.boulder 160 - Generated.soko3_2Potential.boulder 159 + bonus 159 (change p 159 (some 160)))) = true :=
  check_of_implication _ _ (bound675 p)
theorem guard676 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 157 .west = true) : d873 p = 1 := by
  change (!(p 158) && !false && !false) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d873, h158] at guard ⊢
theorem bound676 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 157 .west = true) : bonus 158 p ≤ bonus 157 p := by
  have certified := compare6957 p (guard676 p guard)
  simpa only [at158, at157, Int.zero_add] using certified
theorem check676 (p : Pattern) : (!walkGuard soko3_2.board support p 158 157 .west || decide (bonus 158 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound676 p)
theorem guard677 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 133 .northEast = true) : d1247 p = 1 := by
  change (!(p 158) && !(p 133) && !(true && (p 132) && (p 159))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d873, d1167, d1171, d1243, d1246, d1247, h132, h133, h158, h159] at guard ⊢
theorem bound677 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 133 .northEast = true) : bonus 158 p ≤ bonus 133 p := by
  have certified := compare7085 p (guard677 p guard)
  simpa only [at158, at133, Int.zero_add] using certified
theorem check677 (p : Pattern) : (!walkGuard soko3_2.board support p 158 133 .northEast || decide (bonus 158 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound677 p)
theorem guard678 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 131 .northWest = true) : d873 p = 1 := by
  change (!(p 158) && !false && !(true && (p 132) && false)) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d873, h132, h158] at guard ⊢
theorem bound678 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 131 .northWest = true) : bonus 158 p ≤ bonus 131 p := by
  have certified := compare6957 p (guard678 p guard)
  simpa only [at158, at131, Int.zero_add] using certified
theorem check678 (p : Pattern) : (!walkGuard soko3_2.board support p 158 131 .northWest || decide (bonus 158 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound678 p)
theorem guard679 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 183 .southWest = true) : d873 p = 1 := by
  change (!(p 158) && !false && !(true && true && false)) = true at guard
  cases h158 : p 158
  all_goals simp [d0, d1, d873, h158] at guard ⊢
theorem bound679 (p : Pattern) (guard : walkGuard soko3_2.board support p 158 183 .southWest = true) : bonus 158 p ≤ bonus 183 p := by
  have certified := compare6957 p (guard679 p guard)
  simpa only [at158, at183, Int.zero_add] using certified
theorem check679 (p : Pattern) : (!walkGuard soko3_2.board support p 158 183 .southWest || decide (bonus 158 p ≤ bonus 183 p)) = true :=
  check_of_implication _ _ (bound679 p)
theorem guard680 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 133 .north = true) : d1174 p = 1 := by
  change (!(p 159) && !(p 133) && !false) = true at guard
  cases h133 : p 133 <;> cases h159 : p 159
  all_goals simp [d0, d1, d1167, d1174, h133, h159] at guard ⊢
theorem bound680 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 133 .north = true) : bonus 159 p ≤ bonus 133 p := by
  have certified := compare7162 p (guard680 p guard)
  simpa only [at159, at133, Int.zero_add] using certified
theorem check680 (p : Pattern) : (!walkGuard soko3_2.board support p 159 133 .north || decide (bonus 159 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound680 p)
theorem guard681 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 160 .east = true) : d1240 p = 1 := by
  change (!(p 159) && !(p 160) && !false) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1240, h159, h160] at guard ⊢
theorem bound681 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 160 .east = true) : bonus 159 p ≤ bonus 160 p := by
  have certified := compare7210 p (guard681 p guard)
  simpa only [at159, at160, Int.zero_add] using certified
theorem check681 (p : Pattern) : (!walkGuard soko3_2.board support p 159 160 .east || decide (bonus 159 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound681 p)
theorem guard682 (p : Pattern) (guard : pushGuard support p 159 160 161 161 = true) : d1553 p = 1 := by
  change (!(p 159) && (!true || (p 160)) && !(p 161) && (!(p 161) || false)) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d985, d1552, d1553, h159, h160, h161] at guard ⊢
theorem bound682 (p : Pattern) (guard : pushGuard support p 159 160 161 161 = true) : bonus 159 p ≤ 1 + Generated.soko3_2Potential.boulder 161 - Generated.soko3_2Potential.boulder 160 + bonus 160 (change p 160 (some 161)) := by
  have certified := compare7264 p (guard682 p guard)
  change d696 p ≤ (0 : Int) + d742 (change p 160 (some 161))
  have normalized := agree742 _ _ (change_representative support p 160 (some 161) 10000 dummy_outside)
  rw [normalized]
  change d696 p ≤ (0 : Int) + d742 (change p 160 (some 161))
  rw [sub2900]
  exact certified
theorem check682 (p : Pattern) : (!pushGuard support p 159 160 161 161 || decide (bonus 159 p ≤ 1 + Generated.soko3_2Potential.boulder 161 - Generated.soko3_2Potential.boulder 160 + bonus 160 (change p 160 (some 161)))) = true :=
  check_of_implication _ _ (bound682 p)
theorem guard683 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 158 .west = true) : d1171 p = 1 := by
  change (!(p 159) && !(p 158) && !false) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d1167, d1171, h158, h159] at guard ⊢
theorem bound683 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 158 .west = true) : bonus 159 p ≤ bonus 158 p := by
  have certified := compare7382 p (guard683 p guard)
  simpa only [at159, at158, Int.zero_add] using certified
theorem check683 (p : Pattern) : (!walkGuard soko3_2.board support p 159 158 .west || decide (bonus 159 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound683 p)
theorem guard684 (p : Pattern) (guard : pushGuard support p 159 158 157 157 = true) : d1412 p = 1 := by
  change (!(p 159) && (!true || (p 158)) && !false && (!false || false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d1167, d1412, h158, h159] at guard ⊢
theorem bound684 (p : Pattern) (guard : pushGuard support p 159 158 157 157 = true) : bonus 159 p ≤ 1 + Generated.soko3_2Potential.boulder 157 - Generated.soko3_2Potential.boulder 158 + bonus 158 (change p 158 (some 157)) := by
  have certified := compare7491 p (guard684 p guard)
  change d696 p ≤ (2 : Int) + d652 (change p 158 (some 157))
  have normalized := agree652 _ _ (change_representative support p 158 (some 157) 10000 dummy_outside)
  rw [normalized]
  change d696 p ≤ (2 : Int) + d652 (change p 158 none)
  rw [sub3033]
  exact certified
theorem check684 (p : Pattern) : (!pushGuard support p 159 158 157 157 || decide (bonus 159 p ≤ 1 + Generated.soko3_2Potential.boulder 157 - Generated.soko3_2Potential.boulder 158 + bonus 158 (change p 158 (some 157)))) = true :=
  check_of_implication _ _ (bound684 p)
theorem guard685 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 134 .northEast = true) : d1254 p = 1 := by
  change (!(p 159) && !(p 134) && !(true && (p 133) && (p 160))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1167, d1240, d1250, d1253, d1254, h133, h134, h159, h160] at guard ⊢
theorem bound685 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 134 .northEast = true) : bonus 159 p ≤ bonus 134 p := by
  have certified := compare7585 p (guard685 p guard)
  simpa only [at159, at134, Int.zero_add] using certified
theorem check685 (p : Pattern) : (!walkGuard soko3_2.board support p 159 134 .northEast || decide (bonus 159 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound685 p)
theorem guard686 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 132 .northWest = true) : d1173 p = 1 := by
  change (!(p 159) && !(p 132) && !(true && (p 133) && (p 158))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d1167, d1171, d1172, d1173, h132, h133, h158, h159] at guard ⊢
theorem bound686 (p : Pattern) (guard : walkGuard soko3_2.board support p 159 132 .northWest = true) : bonus 159 p ≤ bonus 132 p := by
  have certified := compare7686 p (guard686 p guard)
  simpa only [at159, at132, Int.zero_add] using certified
theorem check686 (p : Pattern) : (!walkGuard soko3_2.board support p 159 132 .northWest || decide (bonus 159 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound686 p)
theorem guard687 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 134 .north = true) : d1248 p = 1 := by
  change (!(p 160) && !(p 134) && !false) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1248, h134, h160] at guard ⊢
theorem bound687 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 134 .north = true) : bonus 160 p ≤ bonus 134 p := by
  have certified := compare7775 p (guard687 p guard)
  simpa only [at160, at134, Int.zero_add] using certified
theorem check687 (p : Pattern) : (!walkGuard soko3_2.board support p 160 134 .north || decide (bonus 160 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound687 p)
theorem guard688 (p : Pattern) (guard : pushGuard support p 160 134 108 108 = true) : d918 p = 1 := by
  change (!(p 160) && (!true || (p 134)) && !false && (!false || false)) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d918, h134, h160] at guard ⊢
theorem bound688 (p : Pattern) (guard : pushGuard support p 160 134 108 108 = true) : bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder 108 - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some 108)) := by
  have certified := compare7881 p (guard688 p guard)
  change d742 p ≤ (3 : Int) + d388 (change p 134 (some 108))
  have normalized := agree388 _ _ (change_representative support p 134 (some 108) 10000 dummy_outside)
  rw [normalized]
  change d742 p ≤ (3 : Int) + d388 (change p 134 none)
  rw [sub1780]
  exact certified
theorem check688 (p : Pattern) : (!pushGuard support p 160 134 108 108 || decide (bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder 108 - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some 108)))) = true :=
  check_of_implication _ _ (bound688 p)
theorem guard689 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 161 .east = true) : d1293 p = 1 := by
  change (!(p 160) && !(p 161) && !false) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d985, d1293, h160, h161] at guard ⊢
theorem bound689 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 161 .east = true) : bonus 160 p ≤ bonus 161 p := by
  have certified := compare7970 p (guard689 p guard)
  simpa only [at160, at161, Int.zero_add] using certified
theorem check689 (p : Pattern) : (!walkGuard soko3_2.board support p 160 161 .east || decide (bonus 160 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound689 p)
theorem guard690 (p : Pattern) (guard : pushGuard support p 160 161 162 162 = true) : d1690 p = 1 := by
  change (!(p 160) && (!true || (p 161)) && !false && (!false || false)) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d29, d1690, h160, h161] at guard ⊢
theorem bound690 (p : Pattern) (guard : pushGuard support p 160 161 162 162 = true) : bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.boulder 161 + bonus 161 (change p 161 (some 162)) := by
  have certified := compare8062 p (guard690 p guard)
  change d742 p ≤ (0 : Int) + d825 (change p 161 (some 162))
  have normalized := agree825 _ _ (change_representative support p 161 (some 162) 10000 dummy_outside)
  rw [normalized]
  change d742 p ≤ (0 : Int) + d825 (change p 161 none)
  rw [sub3125]
  exact certified
theorem check690 (p : Pattern) : (!pushGuard support p 160 161 162 162 || decide (bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.boulder 161 + bonus 161 (change p 161 (some 162)))) = true :=
  check_of_implication _ _ (bound690 p)
theorem guard691 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 159 .west = true) : d1240 p = 1 := by
  change (!(p 160) && !(p 159) && !false) = true at guard
  cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1240, h159, h160] at guard ⊢
theorem bound691 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 159 .west = true) : bonus 160 p ≤ bonus 159 p := by
  have certified := compare8110 p (guard691 p guard)
  simpa only [at160, at159, Int.zero_add] using certified
theorem check691 (p : Pattern) : (!walkGuard soko3_2.board support p 160 159 .west || decide (bonus 160 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound691 p)
theorem guard692 (p : Pattern) (guard : pushGuard support p 160 159 158 158 = true) : d1506 p = 1 := by
  change (!(p 160) && (!true || (p 159)) && !(p 158) && (!(p 158) || false)) = true at guard
  cases h158 : p 158 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1505, d1506, h158, h159, h160] at guard ⊢
theorem bound692 (p : Pattern) (guard : pushGuard support p 160 159 158 158 = true) : bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder 158 - Generated.soko3_2Potential.boulder 159 + bonus 159 (change p 159 (some 158)) := by
  have certified := compare8167 p (guard692 p guard)
  change d742 p ≤ (2 : Int) + d696 (change p 159 (some 158))
  have normalized := agree696 _ _ (change_representative support p 159 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d742 p ≤ (2 : Int) + d696 (change p 159 (some 158))
  rw [sub3178]
  exact certified
theorem check692 (p : Pattern) : (!pushGuard support p 160 159 158 158 || decide (bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder 158 - Generated.soko3_2Potential.boulder 159 + bonus 159 (change p 159 (some 158)))) = true :=
  check_of_implication _ _ (bound692 p)
theorem guard693 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 135 .northEast = true) : d1294 p = 1 := by
  change (!(p 160) && !false && !(true && (p 134) && (p 161))) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d917, d985, d1293, d1294, h134, h160, h161] at guard ⊢
theorem bound693 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 135 .northEast = true) : bonus 160 p ≤ bonus 135 p := by
  have certified := compare8287 p (guard693 p guard)
  simpa only [at160, at135, Int.zero_add] using certified
theorem check693 (p : Pattern) : (!walkGuard soko3_2.board support p 160 135 .northEast || decide (bonus 160 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound693 p)
theorem guard694 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 133 .northWest = true) : d1242 p = 1 := by
  change (!(p 160) && !(p 133) && !(true && (p 134) && (p 159))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d917, d1240, d1241, d1242, h133, h134, h159, h160] at guard ⊢
theorem bound694 (p : Pattern) (guard : walkGuard soko3_2.board support p 160 133 .northWest = true) : bonus 160 p ≤ bonus 133 p := by
  have certified := compare8365 p (guard694 p guard)
  simpa only [at160, at133, Int.zero_add] using certified
theorem check694 (p : Pattern) : (!walkGuard soko3_2.board support p 160 133 .northWest || decide (bonus 160 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound694 p)
theorem guard695 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 135 .north = true) : d985 p = 1 := by
  change (!(p 161) && !false && !false) = true at guard
  cases h161 : p 161
  all_goals simp [d0, d1, d985, h161] at guard ⊢
theorem bound695 (p : Pattern) (guard : walkGuard soko3_2.board support p 161 135 .north = true) : bonus 161 p ≤ bonus 135 p := by
  have certified := compare8491 p (guard695 p guard)
  simpa only [at161, at135, Int.zero_add] using certified
theorem check695 (p : Pattern) : (!walkGuard soko3_2.board support p 161 135 .north || decide (bonus 161 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound695 p)
end NetHack.Sokoban32Refined
