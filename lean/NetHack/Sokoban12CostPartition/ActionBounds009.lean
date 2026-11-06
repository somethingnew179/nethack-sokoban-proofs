import NetHack.Sokoban12CostPartition.ActionBounds008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard216 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 105 .northWest = true) : d740 p = 1 := by
  change (!(p 132) && !false && !(true && false && false)) = true at guard
  cases h132 : p 132
  all_goals simp [d0, d1, d740, h132] at guard ⊢
theorem bound216 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 105 .northWest = true) : bonus 132 p ≤ bonus 105 p := by
  have certified := compare372 p (guard216 p guard)
  simpa only [at132, at105, Int.zero_add] using certified
theorem check216 (p : Pattern) : (!walkGuard soko1_2.board support p 132 105 .northWest || decide (bonus 132 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound216 p)
theorem guard217 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 159 .southEast = true) : d800 p = 1 := by
  change (!(p 132) && !(p 159) && !(true && (p 158) && (p 133))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, d798, d799, d800, h132, h133, h158, h159] at guard ⊢
theorem bound217 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 159 .southEast = true) : bonus 132 p ≤ bonus 159 p := by
  have certified := compare516 p (guard217 p guard)
  simpa only [at132, at159, Int.zero_add] using certified
theorem check217 (p : Pattern) : (!walkGuard soko1_2.board support p 132 159 .southEast || decide (bonus 132 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound217 p)
theorem guard218 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 157 .southWest = true) : d740 p = 1 := by
  change (!(p 132) && !false && !(true && (p 158) && false)) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d740, h132, h158] at guard ⊢
theorem bound218 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 157 .southWest = true) : bonus 132 p ≤ bonus 157 p := by
  have certified := compare372 p (guard218 p guard)
  simpa only [at132, at157, Int.zero_add] using certified
theorem check218 (p : Pattern) : (!walkGuard soko1_2.board support p 132 157 .southWest || decide (bonus 132 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound218 p)
theorem guard219 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 159 .south = true) : d801 p = 1 := by
  change (!(p 133) && !(p 159) && !false) = true at guard
  cases h133 : p 133 <;> cases h159 : p 159
  all_goals simp [d0, d1, d794, d801, h133, h159] at guard ⊢
theorem bound219 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 159 .south = true) : bonus 133 p ≤ bonus 159 p := by
  have certified := compare533 p (guard219 p guard)
  simpa only [at133, at159, Int.zero_add] using certified
theorem check219 (p : Pattern) : (!walkGuard soko1_2.board support p 133 159 .south || decide (bonus 133 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound219 p)
theorem guard220 (p : Pattern) (guard : pushGuard support p 133 159 185 185 = true) : d802 p = 1 := by
  change (!(p 133) && (!true || (p 159)) && !false && (!false || false)) = true at guard
  cases h133 : p 133 <;> cases h159 : p 159
  all_goals simp [d0, d1, d793, d802, h133, h159] at guard ⊢
theorem bound220 (p : Pattern) (guard : pushGuard support p 133 159 185 185 = true) : bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some 185)) := by
  have certified := compare559 p (guard220 p guard)
  change d219 p ≤ (2 : Int) + d356 (change p 159 (some 185))
  have normalized := agree356 _ _ (change_representative support p 159 (some 185) 10000 dummy_outside)
  rw [normalized]
  change d219 p ≤ (2 : Int) + d356 (change p 159 none)
  rw [sub567]
  exact certified
theorem check220 (p : Pattern) : (!pushGuard support p 133 159 185 185 || decide (bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some 185)))) = true :=
  check_of_implication _ _ (bound220 p)
theorem guard221 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 134 .east = true) : d765 p = 1 := by
  change (!(p 133) && !(p 134) && !false) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d765, h133, h134] at guard ⊢
theorem bound221 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 134 .east = true) : bonus 133 p ≤ bonus 134 p := by
  have certified := compare572 p (guard221 p guard)
  simpa only [at133, at134, Int.zero_add] using certified
theorem check221 (p : Pattern) : (!walkGuard soko1_2.board support p 133 134 .east || decide (bonus 133 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound221 p)
theorem guard222 (p : Pattern) (guard : pushGuard support p 133 134 135 135 = true) : d810 p = 1 := by
  change (!(p 133) && (!true || (p 134)) && !false && (!false || false)) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d736, d810, h133, h134] at guard ⊢
theorem bound222 (p : Pattern) (guard : pushGuard support p 133 134 135 135 = true) : bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder 135 - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some 135)) := by
  have certified := compare622 p (guard222 p guard)
  change d219 p ≤ (14 : Int) + d74 (change p 134 (some 135))
  have normalized := agree74 _ _ (change_representative support p 134 (some 135) 10000 dummy_outside)
  rw [normalized]
  change d219 p ≤ (14 : Int) + d74 (change p 134 none)
  rw [sub601]
  exact certified
theorem check222 (p : Pattern) : (!pushGuard support p 133 134 135 135 || decide (bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder 135 - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some 135)))) = true :=
  check_of_implication _ _ (bound222 p)
theorem guard223 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 132 .west = true) : d754 p = 1 := by
  change (!(p 133) && !(p 132) && !false) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d753, d754, h132, h133] at guard ⊢
theorem bound223 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 132 .west = true) : bonus 133 p ≤ bonus 132 p := by
  have certified := compare629 p (guard223 p guard)
  simpa only [at133, at132, Int.zero_add] using certified
theorem check223 (p : Pattern) : (!walkGuard soko1_2.board support p 133 132 .west || decide (bonus 133 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound223 p)
theorem guard224 (p : Pattern) (guard : pushGuard support p 133 132 131 131 = true) : d771 p = 1 := by
  change (!(p 133) && (!true || (p 132)) && !false && (!false || false)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d753, d771, h132, h133] at guard ⊢
theorem bound224 (p : Pattern) (guard : pushGuard support p 133 132 131 131 = true) : bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder 131 - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some 131)) := by
  have certified := compare676 p (guard224 p guard)
  change d219 p ≤ (12 : Int) + d201 (change p 132 (some 131))
  have normalized := agree201 _ _ (change_representative support p 132 (some 131) 10000 dummy_outside)
  rw [normalized]
  change d219 p ≤ (12 : Int) + d201 (change p 132 none)
  rw [sub676]
  exact certified
theorem check224 (p : Pattern) : (!pushGuard support p 133 132 131 131 || decide (bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder 131 - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some 131)))) = true :=
  check_of_implication _ _ (bound224 p)
theorem guard225 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 108 .northEast = true) : d766 p = 1 := by
  change (!(p 133) && !(p 108) && !(true && true && (p 134))) = true at guard
  cases h108 : p 108 <;> cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d765, d766, h108, h133, h134] at guard ⊢
theorem bound225 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 108 .northEast = true) : bonus 133 p ≤ bonus 108 p := by
  have certified := compare678 p (guard225 p guard)
  simpa only [at133, at108, Int.zero_add] using certified
theorem check225 (p : Pattern) : (!walkGuard soko1_2.board support p 133 108 .northEast || decide (bonus 133 p ≤ bonus 108 p)) = true :=
  check_of_implication _ _ (bound225 p)
theorem guard226 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 106 .northWest = true) : d754 p = 1 := by
  change (!(p 133) && !false && !(true && true && (p 132))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d753, d754, h132, h133] at guard ⊢
theorem bound226 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 106 .northWest = true) : bonus 133 p ≤ bonus 106 p := by
  have certified := compare683 p (guard226 p guard)
  simpa only [at133, at106, Int.zero_add] using certified
theorem check226 (p : Pattern) : (!walkGuard soko1_2.board support p 133 106 .northWest || decide (bonus 133 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound226 p)
theorem guard227 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 160 .southEast = true) : d820 p = 1 := by
  change (!(p 133) && !(p 160) && !(true && (p 159) && (p 134))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d818, d819, d820, h133, h134, h159, h160] at guard ⊢
theorem bound227 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 160 .southEast = true) : bonus 133 p ≤ bonus 160 p := by
  have certified := compare722 p (guard227 p guard)
  simpa only [at133, at160, Int.zero_add] using certified
theorem check227 (p : Pattern) : (!walkGuard soko1_2.board support p 133 160 .southEast || decide (bonus 133 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound227 p)
theorem guard228 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 158 .southWest = true) : d825 p = 1 := by
  change (!(p 133) && !(p 158) && !(true && (p 159) && (p 132))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d742, d794, d798, d821, d824, d825, h132, h133, h158, h159] at guard ⊢
theorem bound228 (p : Pattern) (guard : walkGuard soko1_2.board support p 133 158 .southWest = true) : bonus 133 p ≤ bonus 158 p := by
  have certified := compare750 p (guard228 p guard)
  simpa only [at133, at158, Int.zero_add] using certified
theorem check228 (p : Pattern) : (!walkGuard soko1_2.board support p 133 158 .southWest || decide (bonus 133 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound228 p)
theorem guard229 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 108 .north = true) : d755 p = 1 := by
  change (!(p 134) && !(p 108) && !false) = true at guard
  cases h108 : p 108 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d755, h108, h134] at guard ⊢
theorem bound229 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 108 .north = true) : bonus 134 p ≤ bonus 108 p := by
  have certified := compare752 p (guard229 p guard)
  simpa only [at134, at108, Int.zero_add] using certified
theorem check229 (p : Pattern) : (!walkGuard soko1_2.board support p 134 108 .north || decide (bonus 134 p ≤ bonus 108 p)) = true :=
  check_of_implication _ _ (bound229 p)
theorem guard230 (p : Pattern) (guard : pushGuard support p 134 108 82 82 = true) : d738 p = 1 := by
  change (!(p 134) && (!true || (p 108)) && !false && (!false || false)) = true at guard
  cases h108 : p 108 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d738, h108, h134] at guard ⊢
theorem bound230 (p : Pattern) (guard : pushGuard support p 134 108 82 82 = true) : bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder 82 - Generated.soko1_2Potential.boulder 108 + bonus 108 (change p 108 (some 82)) := by
  have certified := compare753 p (guard230 p guard)
  change d74 p ≤ (0 : Int) + d75 (change p 108 (some 82))
  have normalized := agree75 _ _ (change_representative support p 108 (some 82) 10000 dummy_outside)
  rw [normalized]
  change d74 p ≤ (0 : Int) + d75 (change p 108 none)
  rw [sub711]
  exact certified
theorem check230 (p : Pattern) : (!pushGuard support p 134 108 82 82 || decide (bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder 82 - Generated.soko1_2Potential.boulder 108 + bonus 108 (change p 108 (some 82)))) = true :=
  check_of_implication _ _ (bound230 p)
theorem guard231 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 160 .south = true) : d826 p = 1 := by
  change (!(p 134) && !(p 160) && !false) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d826, h134, h160] at guard ⊢
theorem bound231 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 160 .south = true) : bonus 134 p ≤ bonus 160 p := by
  have certified := compare765 p (guard231 p guard)
  simpa only [at134, at160, Int.zero_add] using certified
theorem check231 (p : Pattern) : (!walkGuard soko1_2.board support p 134 160 .south || decide (bonus 134 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound231 p)
theorem guard232 (p : Pattern) (guard : pushGuard support p 134 160 186 186 = true) : d831 p = 1 := by
  change (!(p 134) && (!true || (p 160)) && !(p 186) && (!(p 186) || false)) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d829, d830, d831, h134, h160, h186] at guard ⊢
theorem bound232 (p : Pattern) (guard : pushGuard support p 134 160 186 186 = true) : bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some 186)) := by
  have certified := compare794 p (guard232 p guard)
  change d74 p ≤ (2 : Int) + d374 (change p 160 (some 186))
  have normalized := agree374 _ _ (change_representative support p 160 (some 186) 10000 dummy_outside)
  rw [normalized]
  change d74 p ≤ (2 : Int) + d374 (change p 160 (some 186))
  rw [sub746]
  exact certified
theorem check232 (p : Pattern) : (!pushGuard support p 134 160 186 186 || decide (bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some 186)))) = true :=
  check_of_implication _ _ (bound232 p)
theorem guard233 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 135 .east = true) : d737 p = 1 := by
  change (!(p 134) && !false && !false) = true at guard
  cases h134 : p 134
  all_goals simp [d0, d1, d737, h134] at guard ⊢
theorem bound233 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 135 .east = true) : bonus 134 p ≤ bonus 135 p := by
  have certified := compare795 p (guard233 p guard)
  simpa only [at134, at135, Int.zero_add] using certified
theorem check233 (p : Pattern) : (!walkGuard soko1_2.board support p 134 135 .east || decide (bonus 134 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound233 p)
theorem guard234 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 133 .west = true) : d765 p = 1 := by
  change (!(p 134) && !(p 133) && !false) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d765, h133, h134] at guard ⊢
theorem bound234 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 133 .west = true) : bonus 134 p ≤ bonus 133 p := by
  have certified := compare798 p (guard234 p guard)
  simpa only [at134, at133, Int.zero_add] using certified
theorem check234 (p : Pattern) : (!walkGuard soko1_2.board support p 134 133 .west || decide (bonus 134 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound234 p)
theorem guard235 (p : Pattern) (guard : pushGuard support p 134 133 132 132 = true) : d790 p = 1 := by
  change (!(p 134) && (!true || (p 133)) && !(p 132) && (!(p 132) || false)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d789, d790, h132, h133, h134] at guard ⊢
theorem bound235 (p : Pattern) (guard : pushGuard support p 134 133 132 132 = true) : bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder 132 - Generated.soko1_2Potential.boulder 133 + bonus 133 (change p 133 (some 132)) := by
  have certified := compare811 p (guard235 p guard)
  change d74 p ≤ (2 : Int) + d219 (change p 133 (some 132))
  have normalized := agree219 _ _ (change_representative support p 133 (some 132) 10000 dummy_outside)
  rw [normalized]
  change d74 p ≤ (2 : Int) + d219 (change p 133 (some 132))
  rw [sub788]
  exact certified
theorem check235 (p : Pattern) : (!pushGuard support p 134 133 132 132 || decide (bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder 132 - Generated.soko1_2Potential.boulder 133 + bonus 133 (change p 133 (some 132)))) = true :=
  check_of_implication _ _ (bound235 p)
theorem guard236 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 161 .southEast = true) : d737 p = 1 := by
  change (!(p 134) && !false && !(true && (p 160) && false)) = true at guard
  cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d737, h134, h160] at guard ⊢
theorem bound236 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 161 .southEast = true) : bonus 134 p ≤ bonus 161 p := by
  have certified := compare795 p (guard236 p guard)
  simpa only [at134, at161, Int.zero_add] using certified
theorem check236 (p : Pattern) : (!walkGuard soko1_2.board support p 134 161 .southEast || decide (bonus 134 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound236 p)
theorem guard237 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 159 .southWest = true) : d849 p = 1 := by
  change (!(p 134) && !(p 159) && !(true && (p 160) && (p 133))) = true at guard
  cases h133 : p 133 <;> cases h134 : p 134 <;> cases h159 : p 159 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d794, d818, d845, d848, d849, h133, h134, h159, h160] at guard ⊢
theorem bound237 (p : Pattern) (guard : walkGuard soko1_2.board support p 134 159 .southWest = true) : bonus 134 p ≤ bonus 159 p := by
  have certified := compare842 p (guard237 p guard)
  simpa only [at134, at159, Int.zero_add] using certified
theorem check237 (p : Pattern) : (!walkGuard soko1_2.board support p 134 159 .southWest || decide (bonus 134 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound237 p)
theorem guard238 (p : Pattern) (guard : walkGuard soko1_2.board support p 135 161 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound238 (p : Pattern) (guard : walkGuard soko1_2.board support p 135 161 .south = true) : bonus 135 p ≤ bonus 161 p := by
  have certified := compare843 p (guard238 p guard)
  simpa only [at135, at161, Int.zero_add] using certified
theorem check238 (p : Pattern) : (!walkGuard soko1_2.board support p 135 161 .south || decide (bonus 135 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound238 p)
theorem guard239 (p : Pattern) (guard : pushGuard support p 135 161 187 187 = true) : d851 p = 1 := by
  change (!false && (!false || false) && !(p 187) && (!(p 187) || false)) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound239 (p : Pattern) (guard : pushGuard support p 135 161 187 187 = true) : bonus 135 p ≤ 1 + Generated.soko1_2Potential.boulder 187 - Generated.soko1_2Potential.boulder 161 + bonus 161 (change p 161 (some 187)) := by
  have certified := compare844 p (guard239 p guard)
  change d236 p ≤ (0 : Int) + d236 (change p 161 (some 187))
  have normalized := agree236 _ _ (change_representative support p 161 (some 187) 10000 dummy_outside)
  rw [normalized]
  change d236 p ≤ (0 : Int) + d236 (change p 10000 (some 187))
  rw [sub834]
  exact certified
theorem check239 (p : Pattern) : (!pushGuard support p 135 161 187 187 || decide (bonus 135 p ≤ 1 + Generated.soko1_2Potential.boulder 187 - Generated.soko1_2Potential.boulder 161 + bonus 161 (change p 161 (some 187)))) = true :=
  check_of_implication _ _ (bound239 p)
end NetHack.Sokoban12CostPartition
