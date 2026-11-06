import NetHack.Sokoban12CostPartition.ActionBounds007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard192 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 115 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound192 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 115 .west = true) : bonus 116 p ≤ bonus 115 p := by
  have certified := compare245 p (guard192 p guard)
  simpa only [at116, at115, Int.zero_add] using certified
theorem check192 (p : Pattern) : (!walkGuard soko1_2.board support p 116 115 .west || decide (bonus 116 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound192 p)
theorem guard193 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 143 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound193 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 143 .southEast = true) : bonus 116 p ≤ bonus 143 p := by
  have certified := compare245 p (guard193 p guard)
  simpa only [at116, at143, Int.zero_add] using certified
theorem check193 (p : Pattern) : (!walkGuard soko1_2.board support p 116 143 .southEast || decide (bonus 116 p ≤ bonus 143 p)) = true :=
  check_of_implication _ _ (bound193 p)
theorem guard194 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 141 .southWest = true) : d768 p = 1 := by
  change (!false && !(p 141) && !(true && false && false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound194 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 141 .southWest = true) : bonus 116 p ≤ bonus 141 p := by
  have certified := compare243 p (guard194 p guard)
  simpa only [at116, at141, Int.zero_add] using certified
theorem check194 (p : Pattern) : (!walkGuard soko1_2.board support p 116 141 .southWest || decide (bonus 116 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound194 p)
theorem guard195 (p : Pattern) (guard : walkGuard soko1_2.board support p 117 143 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound195 (p : Pattern) (guard : walkGuard soko1_2.board support p 117 143 .south = true) : bonus 117 p ≤ bonus 143 p := by
  have certified := compare245 p (guard195 p guard)
  simpa only [at117, at143, Int.zero_add] using certified
theorem check195 (p : Pattern) : (!walkGuard soko1_2.board support p 117 143 .south || decide (bonus 117 p ≤ bonus 143 p)) = true :=
  check_of_implication _ _ (bound195 p)
theorem guard196 (p : Pattern) (guard : pushGuard support p 117 143 169 169 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound196 (p : Pattern) (guard : pushGuard support p 117 143 169 169 = true) : bonus 117 p ≤ 1 + Generated.soko1_2Potential.boulder 169 - Generated.soko1_2Potential.boulder 143 + bonus 143 (change p 143 (some 169)) := by
  have certified := compare246 p (guard196 p guard)
  change d195 p ≤ (1 : Int) + d195 (change p 143 (some 169))
  have normalized := agree195 _ _ (change_representative support p 143 (some 169) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (1 : Int) + d195 (change p 10000 none)
  rw [sub285]
  exact certified
theorem check196 (p : Pattern) : (!pushGuard support p 117 143 169 169 || decide (bonus 117 p ≤ 1 + Generated.soko1_2Potential.boulder 169 - Generated.soko1_2Potential.boulder 143 + bonus 143 (change p 143 (some 169)))) = true :=
  check_of_implication _ _ (bound196 p)
theorem guard197 (p : Pattern) (guard : walkGuard soko1_2.board support p 117 116 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound197 (p : Pattern) (guard : walkGuard soko1_2.board support p 117 116 .west = true) : bonus 117 p ≤ bonus 116 p := by
  have certified := compare245 p (guard197 p guard)
  simpa only [at117, at116, Int.zero_add] using certified
theorem check197 (p : Pattern) : (!walkGuard soko1_2.board support p 117 116 .west || decide (bonus 117 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound197 p)
theorem guard198 (p : Pattern) (guard : pushGuard support p 117 116 115 115 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound198 (p : Pattern) (guard : pushGuard support p 117 116 115 115 = true) : bonus 117 p ≤ 1 + Generated.soko1_2Potential.boulder 115 - Generated.soko1_2Potential.boulder 116 + bonus 116 (change p 116 (some 115)) := by
  have certified := compare246 p (guard198 p guard)
  change d195 p ≤ (1 : Int) + d195 (change p 116 (some 115))
  have normalized := agree195 _ _ (change_representative support p 116 (some 115) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (1 : Int) + d195 (change p 10000 none)
  rw [sub285]
  exact certified
theorem check198 (p : Pattern) : (!pushGuard support p 117 116 115 115 || decide (bonus 117 p ≤ 1 + Generated.soko1_2Potential.boulder 115 - Generated.soko1_2Potential.boulder 116 + bonus 116 (change p 116 (some 115)))) = true :=
  check_of_implication _ _ (bound198 p)
theorem guard199 (p : Pattern) (guard : walkGuard soko1_2.board support p 117 142 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound199 (p : Pattern) (guard : walkGuard soko1_2.board support p 117 142 .southWest = true) : bonus 117 p ≤ bonus 142 p := by
  have certified := compare245 p (guard199 p guard)
  simpa only [at117, at142, Int.zero_add] using certified
theorem check199 (p : Pattern) : (!walkGuard soko1_2.board support p 117 142 .southWest || decide (bonus 117 p ≤ bonus 142 p)) = true :=
  check_of_implication _ _ (bound199 p)
theorem guard200 (p : Pattern) (guard : walkGuard soko1_2.board support p 128 102 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound200 (p : Pattern) (guard : walkGuard soko1_2.board support p 128 102 .north = true) : bonus 128 p ≤ bonus 102 p := by
  have certified := compare0 p (guard200 p guard)
  simpa only [at128, at102, Int.zero_add] using certified
theorem check200 (p : Pattern) : (!walkGuard soko1_2.board support p 128 102 .north || decide (bonus 128 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound200 p)
theorem guard201 (p : Pattern) (guard : pushGuard support p 128 102 76 76 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound201 (p : Pattern) (guard : pushGuard support p 128 102 76 76 = true) : bonus 128 p ≤ 1 + Generated.soko1_2Potential.boulder 76 - Generated.soko1_2Potential.boulder 102 + bonus 102 (change p 102 (some 76)) := by
  have certified := compare3 p (guard201 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 102 (some 76))
  have normalized := agree75 _ _ (change_representative support p 102 (some 76) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check201 (p : Pattern) : (!pushGuard support p 128 102 76 76 || decide (bonus 128 p ≤ 1 + Generated.soko1_2Potential.boulder 76 - Generated.soko1_2Potential.boulder 102 + bonus 102 (change p 102 (some 76)))) = true :=
  check_of_implication _ _ (bound201 p)
theorem guard202 (p : Pattern) (guard : walkGuard soko1_2.board support p 128 154 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound202 (p : Pattern) (guard : walkGuard soko1_2.board support p 128 154 .south = true) : bonus 128 p ≤ bonus 154 p := by
  have certified := compare0 p (guard202 p guard)
  simpa only [at128, at154, Int.zero_add] using certified
theorem check202 (p : Pattern) : (!walkGuard soko1_2.board support p 128 154 .south || decide (bonus 128 p ≤ bonus 154 p)) = true :=
  check_of_implication _ _ (bound202 p)
theorem guard203 (p : Pattern) (guard : pushGuard support p 128 154 180 180 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound203 (p : Pattern) (guard : pushGuard support p 128 154 180 180 = true) : bonus 128 p ≤ 1 + Generated.soko1_2Potential.boulder 180 - Generated.soko1_2Potential.boulder 154 + bonus 154 (change p 154 (some 180)) := by
  have certified := compare3 p (guard203 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 154 (some 180))
  have normalized := agree75 _ _ (change_representative support p 154 (some 180) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check203 (p : Pattern) : (!pushGuard support p 128 154 180 180 || decide (bonus 128 p ≤ 1 + Generated.soko1_2Potential.boulder 180 - Generated.soko1_2Potential.boulder 154 + bonus 154 (change p 154 (some 180)))) = true :=
  check_of_implication _ _ (bound203 p)
theorem guard204 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 105 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound204 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 105 .north = true) : bonus 131 p ≤ bonus 105 p := by
  have certified := compare40 p (guard204 p guard)
  simpa only [at131, at105, Int.zero_add] using certified
theorem check204 (p : Pattern) : (!walkGuard soko1_2.board support p 131 105 .north || decide (bonus 131 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound204 p)
theorem guard205 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 157 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound205 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 157 .south = true) : bonus 131 p ≤ bonus 157 p := by
  have certified := compare40 p (guard205 p guard)
  simpa only [at131, at157, Int.zero_add] using certified
theorem check205 (p : Pattern) : (!walkGuard soko1_2.board support p 131 157 .south || decide (bonus 131 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound205 p)
theorem guard206 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 132 .east = true) : d740 p = 1 := by
  change (!false && !(p 132) && !false) = true at guard
  cases h132 : p 132
  all_goals simp [d0, d1, d740, h132] at guard ⊢
theorem bound206 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 132 .east = true) : bonus 131 p ≤ bonus 132 p := by
  have certified := compare48 p (guard206 p guard)
  simpa only [at131, at132, Int.zero_add] using certified
theorem check206 (p : Pattern) : (!walkGuard soko1_2.board support p 131 132 .east || decide (bonus 131 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound206 p)
theorem guard207 (p : Pattern) (guard : pushGuard support p 131 132 133 133 = true) : d771 p = 1 := by
  change (!false && (!true || (p 132)) && !(p 133) && (!(p 133) || false)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d753, d771, h132, h133] at guard ⊢
theorem bound207 (p : Pattern) (guard : pushGuard support p 131 132 133 133 = true) : bonus 131 p ≤ 1 + Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some 133)) := by
  have certified := compare317 p (guard207 p guard)
  change d161 p ≤ (0 : Int) + d201 (change p 132 (some 133))
  have normalized := agree201 _ _ (change_representative support p 132 (some 133) 10000 dummy_outside)
  rw [normalized]
  change d161 p ≤ (0 : Int) + d201 (change p 132 (some 133))
  rw [sub389]
  exact certified
theorem check207 (p : Pattern) : (!pushGuard support p 131 132 133 133 || decide (bonus 131 p ≤ 1 + Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some 133)))) = true :=
  check_of_implication _ _ (bound207 p)
theorem guard208 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 106 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 132))) = true at guard
  cases h132 : p 132
  all_goals simp [d1, h132] at guard ⊢
theorem bound208 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 106 .northEast = true) : bonus 131 p ≤ bonus 106 p := by
  have certified := compare40 p (guard208 p guard)
  simpa only [at131, at106, Int.zero_add] using certified
theorem check208 (p : Pattern) : (!walkGuard soko1_2.board support p 131 106 .northEast || decide (bonus 131 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound208 p)
theorem guard209 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 158 .southEast = true) : d742 p = 1 := by
  change (!false && !(p 158) && !(true && false && (p 132))) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d742, h132, h158] at guard ⊢
theorem bound209 (p : Pattern) (guard : walkGuard soko1_2.board support p 131 158 .southEast = true) : bonus 131 p ≤ bonus 158 p := by
  have certified := compare367 p (guard209 p guard)
  simpa only [at131, at158, Int.zero_add] using certified
theorem check209 (p : Pattern) : (!walkGuard soko1_2.board support p 131 158 .southEast || decide (bonus 131 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound209 p)
theorem guard210 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 106 .north = true) : d740 p = 1 := by
  change (!(p 132) && !false && !false) = true at guard
  cases h132 : p 132
  all_goals simp [d0, d1, d740, h132] at guard ⊢
theorem bound210 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 106 .north = true) : bonus 132 p ≤ bonus 106 p := by
  have certified := compare372 p (guard210 p guard)
  simpa only [at132, at106, Int.zero_add] using certified
theorem check210 (p : Pattern) : (!walkGuard soko1_2.board support p 132 106 .north || decide (bonus 132 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound210 p)
theorem guard211 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 158 .south = true) : d773 p = 1 := by
  change (!(p 132) && !(p 158) && !false) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d742, d773, h132, h158] at guard ⊢
theorem bound211 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 158 .south = true) : bonus 132 p ≤ bonus 158 p := by
  have certified := compare377 p (guard211 p guard)
  simpa only [at132, at158, Int.zero_add] using certified
theorem check211 (p : Pattern) : (!walkGuard soko1_2.board support p 132 158 .south || decide (bonus 132 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound211 p)
theorem guard212 (p : Pattern) (guard : pushGuard support p 132 158 184 184 = true) : d774 p = 1 := by
  change (!(p 132) && (!true || (p 158)) && !false && (!false || false)) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d741, d774, h132, h158] at guard ⊢
theorem bound212 (p : Pattern) (guard : pushGuard support p 132 158 184 184 = true) : bonus 132 p ≤ 1 + Generated.soko1_2Potential.boulder 184 - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some 184)) := by
  have certified := compare426 p (guard212 p guard)
  change d201 p ≤ (2 : Int) + d319 (change p 158 (some 184))
  have normalized := agree319 _ _ (change_representative support p 158 (some 184) 10000 dummy_outside)
  rw [normalized]
  change d201 p ≤ (2 : Int) + d319 (change p 158 none)
  rw [sub463]
  exact certified
theorem check212 (p : Pattern) : (!pushGuard support p 132 158 184 184 || decide (bonus 132 p ≤ 1 + Generated.soko1_2Potential.boulder 184 - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some 184)))) = true :=
  check_of_implication _ _ (bound212 p)
theorem guard213 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 133 .east = true) : d754 p = 1 := by
  change (!(p 132) && !(p 133) && !false) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d753, d754, h132, h133] at guard ⊢
theorem bound213 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 133 .east = true) : bonus 132 p ≤ bonus 133 p := by
  have certified := compare431 p (guard213 p guard)
  simpa only [at132, at133, Int.zero_add] using certified
theorem check213 (p : Pattern) : (!walkGuard soko1_2.board support p 132 133 .east || decide (bonus 132 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound213 p)
theorem guard214 (p : Pattern) (guard : pushGuard support p 132 133 134 134 = true) : d790 p = 1 := by
  change (!(p 132) && (!true || (p 133)) && !(p 134) && (!(p 134) || false)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d789, d790, h132, h133, h134] at guard ⊢
theorem bound214 (p : Pattern) (guard : pushGuard support p 132 133 134 134 = true) : bonus 132 p ≤ 1 + Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.boulder 133 + bonus 133 (change p 133 (some 134)) := by
  have certified := compare472 p (guard214 p guard)
  change d201 p ≤ (0 : Int) + d219 (change p 133 (some 134))
  have normalized := agree219 _ _ (change_representative support p 133 (some 134) 10000 dummy_outside)
  rw [normalized]
  change d201 p ≤ (0 : Int) + d219 (change p 133 (some 134))
  rw [sub504]
  exact certified
theorem check214 (p : Pattern) : (!pushGuard support p 132 133 134 134 || decide (bonus 132 p ≤ 1 + Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.boulder 133 + bonus 133 (change p 133 (some 134)))) = true :=
  check_of_implication _ _ (bound214 p)
theorem guard215 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 131 .west = true) : d740 p = 1 := by
  change (!(p 132) && !false && !false) = true at guard
  cases h132 : p 132
  all_goals simp [d0, d1, d740, h132] at guard ⊢
theorem bound215 (p : Pattern) (guard : walkGuard soko1_2.board support p 132 131 .west = true) : bonus 132 p ≤ bonus 131 p := by
  have certified := compare372 p (guard215 p guard)
  simpa only [at132, at131, Int.zero_add] using certified
theorem check215 (p : Pattern) : (!walkGuard soko1_2.board support p 132 131 .west || decide (bonus 132 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound215 p)
end NetHack.Sokoban12CostPartition
