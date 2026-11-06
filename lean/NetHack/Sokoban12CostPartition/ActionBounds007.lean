import NetHack.Sokoban12CostPartition.ActionBounds006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard168 (p : Pattern) (guard : walkGuard soko1_2.board support p 105 131 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound168 (p : Pattern) (guard : walkGuard soko1_2.board support p 105 131 .south = true) : bonus 105 p ≤ bonus 131 p := by
  have certified := compare40 p (guard168 p guard)
  simpa only [at105, at131, Int.zero_add] using certified
theorem check168 (p : Pattern) : (!walkGuard soko1_2.board support p 105 131 .south || decide (bonus 105 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound168 p)
theorem guard169 (p : Pattern) (guard : pushGuard support p 105 131 157 157 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound169 (p : Pattern) (guard : pushGuard support p 105 131 157 157 = true) : bonus 105 p ≤ 1 + Generated.soko1_2Potential.boulder 157 - Generated.soko1_2Potential.boulder 131 + bonus 131 (change p 131 (some 157)) := by
  have certified := compare41 p (guard169 p guard)
  change d161 p ≤ (1 : Int) + d161 (change p 131 (some 157))
  have normalized := agree161 _ _ (change_representative support p 131 (some 157) 10000 dummy_outside)
  rw [normalized]
  change d161 p ≤ (1 : Int) + d161 (change p 10000 none)
  rw [sub121]
  exact certified
theorem check169 (p : Pattern) : (!pushGuard support p 105 131 157 157 || decide (bonus 105 p ≤ 1 + Generated.soko1_2Potential.boulder 157 - Generated.soko1_2Potential.boulder 131 + bonus 131 (change p 131 (some 157)))) = true :=
  check_of_implication _ _ (bound169 p)
theorem guard170 (p : Pattern) (guard : walkGuard soko1_2.board support p 105 106 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound170 (p : Pattern) (guard : walkGuard soko1_2.board support p 105 106 .east = true) : bonus 105 p ≤ bonus 106 p := by
  have certified := compare40 p (guard170 p guard)
  simpa only [at105, at106, Int.zero_add] using certified
theorem check170 (p : Pattern) : (!walkGuard soko1_2.board support p 105 106 .east || decide (bonus 105 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound170 p)
theorem guard171 (p : Pattern) (guard : walkGuard soko1_2.board support p 105 132 .southEast = true) : d740 p = 1 := by
  change (!false && !(p 132) && !(true && false && false)) = true at guard
  cases h132 : p 132
  all_goals simp [d0, d1, d740, h132] at guard ⊢
theorem bound171 (p : Pattern) (guard : walkGuard soko1_2.board support p 105 132 .southEast = true) : bonus 105 p ≤ bonus 132 p := by
  have certified := compare48 p (guard171 p guard)
  simpa only [at105, at132, Int.zero_add] using certified
theorem check171 (p : Pattern) : (!walkGuard soko1_2.board support p 105 132 .southEast || decide (bonus 105 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound171 p)
theorem guard172 (p : Pattern) (guard : walkGuard soko1_2.board support p 106 132 .south = true) : d740 p = 1 := by
  change (!false && !(p 132) && !false) = true at guard
  cases h132 : p 132
  all_goals simp [d0, d1, d740, h132] at guard ⊢
theorem bound172 (p : Pattern) (guard : walkGuard soko1_2.board support p 106 132 .south = true) : bonus 106 p ≤ bonus 132 p := by
  have certified := compare48 p (guard172 p guard)
  simpa only [at106, at132, Int.zero_add] using certified
theorem check172 (p : Pattern) : (!walkGuard soko1_2.board support p 106 132 .south || decide (bonus 106 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound172 p)
theorem guard173 (p : Pattern) (guard : pushGuard support p 106 132 158 158 = true) : d743 p = 1 := by
  change (!false && (!true || (p 132)) && !(p 158) && (!(p 158) || false)) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d742, d743, h132, h158] at guard ⊢
theorem bound173 (p : Pattern) (guard : pushGuard support p 106 132 158 158 = true) : bonus 106 p ≤ 1 + Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some 158)) := by
  have certified := compare151 p (guard173 p guard)
  change d161 p ≤ (2 : Int) + d201 (change p 132 (some 158))
  have normalized := agree201 _ _ (change_representative support p 132 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d161 p ≤ (2 : Int) + d201 (change p 132 (some 158))
  rw [sub190]
  exact certified
theorem check173 (p : Pattern) : (!pushGuard support p 106 132 158 158 || decide (bonus 106 p ≤ 1 + Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some 158)))) = true :=
  check_of_implication _ _ (bound173 p)
theorem guard174 (p : Pattern) (guard : walkGuard soko1_2.board support p 106 105 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound174 (p : Pattern) (guard : walkGuard soko1_2.board support p 106 105 .west = true) : bonus 106 p ≤ bonus 105 p := by
  have certified := compare40 p (guard174 p guard)
  simpa only [at106, at105, Int.zero_add] using certified
theorem check174 (p : Pattern) : (!walkGuard soko1_2.board support p 106 105 .west || decide (bonus 106 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound174 p)
theorem guard175 (p : Pattern) (guard : walkGuard soko1_2.board support p 106 133 .southEast = true) : d754 p = 1 := by
  change (!false && !(p 133) && !(true && (p 132) && true)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d753, d754, h132, h133] at guard ⊢
theorem bound175 (p : Pattern) (guard : walkGuard soko1_2.board support p 106 133 .southEast = true) : bonus 106 p ≤ bonus 133 p := by
  have certified := compare162 p (guard175 p guard)
  simpa only [at106, at133, Int.zero_add] using certified
theorem check175 (p : Pattern) : (!walkGuard soko1_2.board support p 106 133 .southEast || decide (bonus 106 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound175 p)
theorem guard176 (p : Pattern) (guard : walkGuard soko1_2.board support p 106 131 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 132) && false)) = true at guard
  cases h132 : p 132
  all_goals simp [d1, h132] at guard ⊢
theorem bound176 (p : Pattern) (guard : walkGuard soko1_2.board support p 106 131 .southWest = true) : bonus 106 p ≤ bonus 131 p := by
  have certified := compare40 p (guard176 p guard)
  simpa only [at106, at131, Int.zero_add] using certified
theorem check176 (p : Pattern) : (!walkGuard soko1_2.board support p 106 131 .southWest || decide (bonus 106 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound176 p)
theorem guard177 (p : Pattern) (guard : walkGuard soko1_2.board support p 108 82 .north = true) : d735 p = 1 := by
  change (!(p 108) && !false && !false) = true at guard
  cases h108 : p 108
  all_goals simp [d0, d1, d735, h108] at guard ⊢
theorem bound177 (p : Pattern) (guard : walkGuard soko1_2.board support p 108 82 .north = true) : bonus 108 p ≤ bonus 82 p := by
  have certified := compare36 p (guard177 p guard)
  simpa only [at108, at82, Int.zero_add] using certified
theorem check177 (p : Pattern) : (!walkGuard soko1_2.board support p 108 82 .north || decide (bonus 108 p ≤ bonus 82 p)) = true :=
  check_of_implication _ _ (bound177 p)
theorem guard178 (p : Pattern) (guard : pushGuard support p 108 82 56 56 = true) : d735 p = 1 := by
  change (!(p 108) && (!false || false) && !false && (!false || false)) = true at guard
  cases h108 : p 108
  all_goals simp [d0, d1, d735, h108] at guard ⊢
theorem bound178 (p : Pattern) (guard : pushGuard support p 108 82 56 56 = true) : bonus 108 p ≤ 1 + Generated.soko1_2Potential.boulder 56 - Generated.soko1_2Potential.boulder 82 + bonus 82 (change p 82 (some 56)) := by
  have certified := compare36 p (guard178 p guard)
  change d75 p ≤ (0 : Int) + d75 (change p 82 (some 56))
  have normalized := agree75 _ _ (change_representative support p 82 (some 56) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (0 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check178 (p : Pattern) : (!pushGuard support p 108 82 56 56 || decide (bonus 108 p ≤ 1 + Generated.soko1_2Potential.boulder 56 - Generated.soko1_2Potential.boulder 82 + bonus 82 (change p 82 (some 56)))) = true :=
  check_of_implication _ _ (bound178 p)
theorem guard179 (p : Pattern) (guard : walkGuard soko1_2.board support p 108 134 .south = true) : d755 p = 1 := by
  change (!(p 108) && !(p 134) && !false) = true at guard
  cases h108 : p 108 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d755, h108, h134] at guard ⊢
theorem bound179 (p : Pattern) (guard : walkGuard soko1_2.board support p 108 134 .south = true) : bonus 108 p ≤ bonus 134 p := by
  have certified := compare165 p (guard179 p guard)
  simpa only [at108, at134, Int.zero_add] using certified
theorem check179 (p : Pattern) : (!walkGuard soko1_2.board support p 108 134 .south || decide (bonus 108 p ≤ bonus 134 p)) = true :=
  check_of_implication _ _ (bound179 p)
theorem guard180 (p : Pattern) (guard : pushGuard support p 108 134 160 160 = true) : d760 p = 1 := by
  change (!(p 108) && (!true || (p 134)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h108 : p 108 <;> cases h134 : p 134 <;> cases h160 : p 160
  all_goals simp [d0, d1, d758, d759, d760, h108, h134, h160] at guard ⊢
theorem bound180 (p : Pattern) (guard : pushGuard support p 108 134 160 160 = true) : bonus 108 p ≤ 1 + Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some 160)) := by
  have certified := compare185 p (guard180 p guard)
  change d75 p ≤ (2 : Int) + d74 (change p 134 (some 160))
  have normalized := agree74 _ _ (change_representative support p 134 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (2 : Int) + d74 (change p 134 (some 160))
  rw [sub223]
  exact certified
theorem check180 (p : Pattern) : (!pushGuard support p 108 134 160 160 || decide (bonus 108 p ≤ 1 + Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some 160)))) = true :=
  check_of_implication _ _ (bound180 p)
theorem guard181 (p : Pattern) (guard : walkGuard soko1_2.board support p 108 135 .southEast = true) : d755 p = 1 := by
  change (!(p 108) && !false && !(true && (p 134) && true)) = true at guard
  cases h108 : p 108 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d755, h108, h134] at guard ⊢
theorem bound181 (p : Pattern) (guard : walkGuard soko1_2.board support p 108 135 .southEast = true) : bonus 108 p ≤ bonus 135 p := by
  have certified := compare196 p (guard181 p guard)
  simpa only [at108, at135, Int.zero_add] using certified
theorem check181 (p : Pattern) : (!walkGuard soko1_2.board support p 108 135 .southEast || decide (bonus 108 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound181 p)
theorem guard182 (p : Pattern) (guard : walkGuard soko1_2.board support p 108 133 .southWest = true) : d766 p = 1 := by
  change (!(p 108) && !(p 133) && !(true && (p 134) && true)) = true at guard
  cases h108 : p 108 <;> cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d737, d765, d766, h108, h133, h134] at guard ⊢
theorem bound182 (p : Pattern) (guard : walkGuard soko1_2.board support p 108 133 .southWest = true) : bonus 108 p ≤ bonus 133 p := by
  have certified := compare207 p (guard182 p guard)
  simpa only [at108, at133, Int.zero_add] using certified
theorem check182 (p : Pattern) : (!walkGuard soko1_2.board support p 108 133 .southWest || decide (bonus 108 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound182 p)
theorem guard183 (p : Pattern) (guard : walkGuard soko1_2.board support p 115 141 .south = true) : d768 p = 1 := by
  change (!false && !(p 141) && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound183 (p : Pattern) (guard : walkGuard soko1_2.board support p 115 141 .south = true) : bonus 115 p ≤ bonus 141 p := by
  have certified := compare243 p (guard183 p guard)
  simpa only [at115, at141, Int.zero_add] using certified
theorem check183 (p : Pattern) : (!walkGuard soko1_2.board support p 115 141 .south || decide (bonus 115 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound183 p)
theorem guard184 (p : Pattern) (guard : pushGuard support p 115 141 167 167 = true) : d767 p = 1 := by
  change (!false && (!true || (p 141)) && !false && (!false || false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d767, h141] at guard ⊢
theorem bound184 (p : Pattern) (guard : pushGuard support p 115 141 167 167 = true) : bonus 115 p ≤ 1 + Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some 167)) := by
  have certified := compare244 p (guard184 p guard)
  change d195 p ≤ (0 : Int) + d309 (change p 141 (some 167))
  have normalized := agree309 _ _ (change_representative support p 141 (some 167) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (0 : Int) + d309 (change p 141 none)
  rw [sub268]
  exact certified
theorem check184 (p : Pattern) : (!pushGuard support p 115 141 167 167 || decide (bonus 115 p ≤ 1 + Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some 167)))) = true :=
  check_of_implication _ _ (bound184 p)
theorem guard185 (p : Pattern) (guard : walkGuard soko1_2.board support p 115 116 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound185 (p : Pattern) (guard : walkGuard soko1_2.board support p 115 116 .east = true) : bonus 115 p ≤ bonus 116 p := by
  have certified := compare245 p (guard185 p guard)
  simpa only [at115, at116, Int.zero_add] using certified
theorem check185 (p : Pattern) : (!walkGuard soko1_2.board support p 115 116 .east || decide (bonus 115 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound185 p)
theorem guard186 (p : Pattern) (guard : pushGuard support p 115 116 117 117 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound186 (p : Pattern) (guard : pushGuard support p 115 116 117 117 = true) : bonus 115 p ≤ 1 + Generated.soko1_2Potential.boulder 117 - Generated.soko1_2Potential.boulder 116 + bonus 116 (change p 116 (some 117)) := by
  have certified := compare246 p (guard186 p guard)
  change d195 p ≤ (1 : Int) + d195 (change p 116 (some 117))
  have normalized := agree195 _ _ (change_representative support p 116 (some 117) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (1 : Int) + d195 (change p 10000 none)
  rw [sub285]
  exact certified
theorem check186 (p : Pattern) : (!pushGuard support p 115 116 117 117 || decide (bonus 115 p ≤ 1 + Generated.soko1_2Potential.boulder 117 - Generated.soko1_2Potential.boulder 116 + bonus 116 (change p 116 (some 117)))) = true :=
  check_of_implication _ _ (bound186 p)
theorem guard187 (p : Pattern) (guard : walkGuard soko1_2.board support p 115 142 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 141) && false)) = true at guard
  cases h141 : p 141
  all_goals simp [d1, h141] at guard ⊢
theorem bound187 (p : Pattern) (guard : walkGuard soko1_2.board support p 115 142 .southEast = true) : bonus 115 p ≤ bonus 142 p := by
  have certified := compare245 p (guard187 p guard)
  simpa only [at115, at142, Int.zero_add] using certified
theorem check187 (p : Pattern) : (!walkGuard soko1_2.board support p 115 142 .southEast || decide (bonus 115 p ≤ bonus 142 p)) = true :=
  check_of_implication _ _ (bound187 p)
theorem guard188 (p : Pattern) (guard : walkGuard soko1_2.board support p 115 140 .southWest = true) : d768 p = 1 := by
  change (!false && !false && !(true && (p 141) && true)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d768, h141] at guard ⊢
theorem bound188 (p : Pattern) (guard : walkGuard soko1_2.board support p 115 140 .southWest = true) : bonus 115 p ≤ bonus 140 p := by
  have certified := compare274 p (guard188 p guard)
  simpa only [at115, at140, Int.zero_add] using certified
theorem check188 (p : Pattern) : (!walkGuard soko1_2.board support p 115 140 .southWest || decide (bonus 115 p ≤ bonus 140 p)) = true :=
  check_of_implication _ _ (bound188 p)
theorem guard189 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 142 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound189 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 142 .south = true) : bonus 116 p ≤ bonus 142 p := by
  have certified := compare245 p (guard189 p guard)
  simpa only [at116, at142, Int.zero_add] using certified
theorem check189 (p : Pattern) : (!walkGuard soko1_2.board support p 116 142 .south || decide (bonus 116 p ≤ bonus 142 p)) = true :=
  check_of_implication _ _ (bound189 p)
theorem guard190 (p : Pattern) (guard : pushGuard support p 116 142 168 168 = true) : d770 p = 1 := by
  change (!false && (!false || false) && !(p 168) && (!(p 168) || false)) = true at guard
  cases h168 : p 168
  all_goals simp [d0, d1, d770, h168] at guard ⊢
theorem bound190 (p : Pattern) (guard : pushGuard support p 116 142 168 168 = true) : bonus 116 p ≤ 1 + Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some 168)) := by
  have certified := compare275 p (guard190 p guard)
  change d195 p ≤ (1 : Int) + d195 (change p 142 (some 168))
  have normalized := agree195 _ _ (change_representative support p 142 (some 168) 10000 dummy_outside)
  rw [normalized]
  change d195 p ≤ (1 : Int) + d195 (change p 10000 (some 168))
  rw [sub322]
  exact certified
theorem check190 (p : Pattern) : (!pushGuard support p 116 142 168 168 || decide (bonus 116 p ≤ 1 + Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some 168)))) = true :=
  check_of_implication _ _ (bound190 p)
theorem guard191 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 117 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound191 (p : Pattern) (guard : walkGuard soko1_2.board support p 116 117 .east = true) : bonus 116 p ≤ bonus 117 p := by
  have certified := compare245 p (guard191 p guard)
  simpa only [at116, at117, Int.zero_add] using certified
theorem check191 (p : Pattern) : (!walkGuard soko1_2.board support p 116 117 .east || decide (bonus 116 p ≤ bonus 117 p)) = true :=
  check_of_implication _ _ (bound191 p)
end NetHack.Sokoban12CostPartition
