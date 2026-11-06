import NetHack.Sokoban22Refined85.ActionBounds024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard600 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 180 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound600 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 180 .south = true) : bonus 158 p ≤ bonus 180 p := by
  have certified := compare0 p (guard600 p guard)
  simpa only [at158, at180, Int.zero_add] using certified
theorem check600 (p : Pattern) : (!walkGuard soko2_2.board support p 158 180 .south || decide (bonus 158 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound600 p)
theorem guard601 (p : Pattern) (guard : pushGuard support p 158 180 202 202 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound601 (p : Pattern) (guard : pushGuard support p 158 180 202 202 = true) : bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder 202 - Generated.soko2_2Potential.boulder 180 + bonus 180 (change p 180 (some 202)) := by
  have certified := compare0 p (guard601 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 180 (some 202))
  have normalized := agree267 _ _ (change_representative support p 180 (some 202) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check601 (p : Pattern) : (!pushGuard support p 158 180 202 202 || decide (bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder 202 - Generated.soko2_2Potential.boulder 180 + bonus 180 (change p 180 (some 202)))) = true :=
  check_of_implication _ _ (bound601 p)
theorem guard602 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 159 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound602 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 159 .east = true) : bonus 158 p ≤ bonus 159 p := by
  have certified := compare0 p (guard602 p guard)
  simpa only [at158, at159, Int.zero_add] using certified
theorem check602 (p : Pattern) : (!walkGuard soko2_2.board support p 158 159 .east || decide (bonus 158 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound602 p)
theorem guard603 (p : Pattern) (guard : pushGuard support p 158 159 160 160 = true) : d4117 p = 1 := by
  change (!false && (!false || false) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h160 : p 160
  all_goals simp [d0, d1, d4117, h160] at guard ⊢
theorem bound603 (p : Pattern) (guard : pushGuard support p 158 159 160 160 = true) : bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.boulder 159 + bonus 159 (change p 159 (some 160)) := by
  have certified := compare4597 p (guard603 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 159 (some 160))
  have normalized := agree267 _ _ (change_representative support p 159 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 (some 160))
  rw [sub4232]
  exact certified
theorem check603 (p : Pattern) : (!pushGuard support p 158 159 160 160 || decide (bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.boulder 159 + bonus 159 (change p 159 (some 160)))) = true :=
  check_of_implication _ _ (bound603 p)
theorem guard604 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 157 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound604 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 157 .west = true) : bonus 158 p ≤ bonus 157 p := by
  have certified := compare0 p (guard604 p guard)
  simpa only [at158, at157, Int.zero_add] using certified
theorem check604 (p : Pattern) : (!walkGuard soko2_2.board support p 158 157 .west || decide (bonus 158 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound604 p)
theorem guard605 (p : Pattern) (guard : pushGuard support p 158 157 156 156 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound605 (p : Pattern) (guard : pushGuard support p 158 157 156 156 = true) : bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder 156 - Generated.soko2_2Potential.boulder 157 + bonus 157 (change p 157 (some 156)) := by
  have certified := compare2458 p (guard605 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 157 (some 156))
  have normalized := agree267 _ _ (change_representative support p 157 (some 156) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check605 (p : Pattern) : (!pushGuard support p 158 157 156 156 || decide (bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder 156 - Generated.soko2_2Potential.boulder 157 + bonus 157 (change p 157 (some 156)))) = true :=
  check_of_implication _ _ (bound605 p)
theorem guard606 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 135 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound606 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 135 .northWest = true) : bonus 158 p ≤ bonus 135 p := by
  have certified := compare0 p (guard606 p guard)
  simpa only [at158, at135, Int.zero_add] using certified
theorem check606 (p : Pattern) : (!walkGuard soko2_2.board support p 158 135 .northWest || decide (bonus 158 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound606 p)
theorem guard607 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 181 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound607 (p : Pattern) (guard : walkGuard soko2_2.board support p 158 181 .southEast = true) : bonus 158 p ≤ bonus 181 p := by
  have certified := compare0 p (guard607 p guard)
  simpa only [at158, at181, Int.zero_add] using certified
theorem check607 (p : Pattern) : (!walkGuard soko2_2.board support p 158 181 .southEast || decide (bonus 158 p ≤ bonus 181 p)) = true :=
  check_of_implication _ _ (bound607 p)
theorem guard608 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 181 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound608 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 181 .south = true) : bonus 159 p ≤ bonus 181 p := by
  have certified := compare0 p (guard608 p guard)
  simpa only [at159, at181, Int.zero_add] using certified
theorem check608 (p : Pattern) : (!walkGuard soko2_2.board support p 159 181 .south || decide (bonus 159 p ≤ bonus 181 p)) = true :=
  check_of_implication _ _ (bound608 p)
theorem guard609 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 160 .east = true) : d4117 p = 1 := by
  change (!false && !(p 160) && !false) = true at guard
  cases h160 : p 160
  all_goals simp [d0, d1, d4117, h160] at guard ⊢
theorem bound609 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 160 .east = true) : bonus 159 p ≤ bonus 160 p := by
  have certified := compare4686 p (guard609 p guard)
  simpa only [at159, at160, Int.zero_add] using certified
theorem check609 (p : Pattern) : (!walkGuard soko2_2.board support p 159 160 .east || decide (bonus 159 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound609 p)
theorem guard610 (p : Pattern) (guard : pushGuard support p 159 160 161 161 = true) : d4432 p = 1 := by
  change (!false && (!true || (p 160)) && !(p 161) && (!(p 161) || false)) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d4299, d4432, h160, h161] at guard ⊢
theorem bound610 (p : Pattern) (guard : pushGuard support p 159 160 161 161 = true) : bonus 159 p ≤ 1 + Generated.soko2_2Potential.boulder 161 - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some 161)) := by
  have certified := compare4966 p (guard610 p guard)
  change d267 p ≤ (2 : Int) + d789 (change p 160 (some 161))
  have normalized := agree789 _ _ (change_representative support p 160 (some 161) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d789 (change p 160 (some 161))
  rw [sub4401]
  exact certified
theorem check610 (p : Pattern) : (!pushGuard support p 159 160 161 161 || decide (bonus 159 p ≤ 1 + Generated.soko2_2Potential.boulder 161 - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some 161)))) = true :=
  check_of_implication _ _ (bound610 p)
theorem guard611 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 158 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound611 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 158 .west = true) : bonus 159 p ≤ bonus 158 p := by
  have certified := compare0 p (guard611 p guard)
  simpa only [at159, at158, Int.zero_add] using certified
theorem check611 (p : Pattern) : (!walkGuard soko2_2.board support p 159 158 .west || decide (bonus 159 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound611 p)
theorem guard612 (p : Pattern) (guard : pushGuard support p 159 158 157 157 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound612 (p : Pattern) (guard : pushGuard support p 159 158 157 157 = true) : bonus 159 p ≤ 1 + Generated.soko2_2Potential.boulder 157 - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some 157)) := by
  have certified := compare2458 p (guard612 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 158 (some 157))
  have normalized := agree267 _ _ (change_representative support p 158 (some 157) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check612 (p : Pattern) : (!pushGuard support p 159 158 157 157 || decide (bonus 159 p ≤ 1 + Generated.soko2_2Potential.boulder 157 - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some 157)))) = true :=
  check_of_implication _ _ (bound612 p)
theorem guard613 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 138 .northEast = true) : d4203 p = 1 := by
  change (!false && !(p 138) && !(true && true && (p 160))) = true at guard
  cases h138 : p 138 <;> cases h160 : p 160
  all_goals simp [d0, d1, d4117, d4203, h138, h160] at guard ⊢
theorem bound613 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 138 .northEast = true) : bonus 159 p ≤ bonus 138 p := by
  have certified := compare5042 p (guard613 p guard)
  simpa only [at159, at138, Int.zero_add] using certified
theorem check613 (p : Pattern) : (!walkGuard soko2_2.board support p 159 138 .northEast || decide (bonus 159 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound613 p)
theorem guard614 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 136 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound614 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 136 .northWest = true) : bonus 159 p ≤ bonus 136 p := by
  have certified := compare0 p (guard614 p guard)
  simpa only [at159, at136, Int.zero_add] using certified
theorem check614 (p : Pattern) : (!walkGuard soko2_2.board support p 159 136 .northWest || decide (bonus 159 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound614 p)
theorem guard615 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 182 .southEast = true) : d4206 p = 1 := by
  change (!false && !(p 182) && !(true && false && (p 160))) = true at guard
  cases h160 : p 160 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4206, h160, h182] at guard ⊢
theorem bound615 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 182 .southEast = true) : bonus 159 p ≤ bonus 182 p := by
  have certified := compare5328 p (guard615 p guard)
  simpa only [at159, at182, Int.zero_add] using certified
theorem check615 (p : Pattern) : (!walkGuard soko2_2.board support p 159 182 .southEast || decide (bonus 159 p ≤ bonus 182 p)) = true :=
  check_of_implication _ _ (bound615 p)
theorem guard616 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 180 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound616 (p : Pattern) (guard : walkGuard soko2_2.board support p 159 180 .southWest = true) : bonus 159 p ≤ bonus 180 p := by
  have certified := compare0 p (guard616 p guard)
  simpa only [at159, at180, Int.zero_add] using certified
theorem check616 (p : Pattern) : (!walkGuard soko2_2.board support p 159 180 .southWest || decide (bonus 159 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound616 p)
theorem guard617 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 138 .north = true) : d4203 p = 1 := by
  change (!(p 160) && !(p 138) && !false) = true at guard
  cases h138 : p 138 <;> cases h160 : p 160
  all_goals simp [d0, d1, d4117, d4203, h138, h160] at guard ⊢
theorem bound617 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 138 .north = true) : bonus 160 p ≤ bonus 138 p := by
  have certified := compare5447 p (guard617 p guard)
  simpa only [at160, at138, Int.zero_add] using certified
theorem check617 (p : Pattern) : (!walkGuard soko2_2.board support p 160 138 .north || decide (bonus 160 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound617 p)
theorem guard618 (p : Pattern) (guard : pushGuard support p 160 138 116 116 = true) : d4119 p = 1 := by
  change (!(p 160) && (!true || (p 138)) && !(p 116) && (!(p 116) || false)) = true at guard
  cases h116 : p 116 <;> cases h138 : p 138 <;> cases h160 : p 160
  all_goals simp [d0, d1, d4117, d4118, d4119, h116, h138, h160] at guard ⊢
theorem bound618 (p : Pattern) (guard : pushGuard support p 160 138 116 116 = true) : bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder 116 - Generated.soko2_2Potential.boulder 138 + bonus 138 (change p 138 (some 116)) := by
  have certified := compare5533 p (guard618 p guard)
  change d789 p ≤ (2 : Int) + d652 (change p 138 (some 116))
  have normalized := agree652 _ _ (change_representative support p 138 (some 116) 10000 dummy_outside)
  rw [normalized]
  change d789 p ≤ (2 : Int) + d652 (change p 138 (some 116))
  rw [sub4637]
  exact certified
theorem check618 (p : Pattern) : (!pushGuard support p 160 138 116 116 || decide (bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder 116 - Generated.soko2_2Potential.boulder 138 + bonus 138 (change p 138 (some 116)))) = true :=
  check_of_implication _ _ (bound618 p)
theorem guard619 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 182 .south = true) : d4471 p = 1 := by
  change (!(p 160) && !(p 182) && !false) = true at guard
  cases h160 : p 160 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4206, d4471, h160, h182] at guard ⊢
theorem bound619 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 182 .south = true) : bonus 160 p ≤ bonus 182 p := by
  have certified := compare5655 p (guard619 p guard)
  simpa only [at160, at182, Int.zero_add] using certified
theorem check619 (p : Pattern) : (!walkGuard soko2_2.board support p 160 182 .south || decide (bonus 160 p ≤ bonus 182 p)) = true :=
  check_of_implication _ _ (bound619 p)
theorem guard620 (p : Pattern) (guard : pushGuard support p 160 182 204 204 = true) : d4476 p = 1 := by
  change (!(p 160) && (!true || (p 182)) && !(p 204) && (!(p 204) || false)) = true at guard
  cases h160 : p 160 <;> cases h182 : p 182 <;> cases h204 : p 204
  all_goals simp [d0, d1, d4474, d4475, d4476, h160, h182, h204] at guard ⊢
theorem bound620 (p : Pattern) (guard : pushGuard support p 160 182 204 204 = true) : bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder 204 - Generated.soko2_2Potential.boulder 182 + bonus 182 (change p 182 (some 204)) := by
  have certified := compare5877 p (guard620 p guard)
  change d789 p ≤ (0 : Int) + d1681 (change p 182 (some 204))
  have normalized := agree1681 _ _ (change_representative support p 182 (some 204) 10000 dummy_outside)
  rw [normalized]
  change d789 p ≤ (0 : Int) + d1681 (change p 182 (some 204))
  rw [sub4888]
  exact certified
theorem check620 (p : Pattern) : (!pushGuard support p 160 182 204 204 || decide (bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder 204 - Generated.soko2_2Potential.boulder 182 + bonus 182 (change p 182 (some 204)))) = true :=
  check_of_implication _ _ (bound620 p)
theorem guard621 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 161 .east = true) : d4301 p = 1 := by
  change (!(p 160) && !(p 161) && !false) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d4299, d4301, h160, h161] at guard ⊢
theorem bound621 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 161 .east = true) : bonus 160 p ≤ bonus 161 p := by
  have certified := compare6007 p (guard621 p guard)
  simpa only [at160, at161, Int.zero_add] using certified
theorem check621 (p : Pattern) : (!walkGuard soko2_2.board support p 160 161 .east || decide (bonus 160 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound621 p)
theorem guard622 (p : Pattern) (guard : pushGuard support p 160 161 162 162 = true) : d4618 p = 1 := by
  change (!(p 160) && (!true || (p 161)) && !(p 162) && (!(p 162) || false)) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161 <;> cases h162 : p 162
  all_goals simp [d0, d1, d4395, d4617, d4618, h160, h161, h162] at guard ⊢
theorem bound622 (p : Pattern) (guard : pushGuard support p 160 161 162 162 = true) : bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder 162 - Generated.soko2_2Potential.boulder 161 + bonus 161 (change p 161 (some 162)) := by
  have certified := compare6190 p (guard622 p guard)
  change d789 p ≤ (2 : Int) + d948 (change p 161 (some 162))
  have normalized := agree948 _ _ (change_representative support p 161 (some 162) 10000 dummy_outside)
  rw [normalized]
  change d789 p ≤ (2 : Int) + d948 (change p 161 (some 162))
  rw [sub5138]
  exact certified
theorem check622 (p : Pattern) : (!pushGuard support p 160 161 162 162 || decide (bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder 162 - Generated.soko2_2Potential.boulder 161 + bonus 161 (change p 161 (some 162)))) = true :=
  check_of_implication _ _ (bound622 p)
theorem guard623 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 159 .west = true) : d4117 p = 1 := by
  change (!(p 160) && !false && !false) = true at guard
  cases h160 : p 160
  all_goals simp [d0, d1, d4117, h160] at guard ⊢
theorem bound623 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 159 .west = true) : bonus 160 p ≤ bonus 159 p := by
  have certified := compare6274 p (guard623 p guard)
  simpa only [at160, at159, Int.zero_add] using certified
theorem check623 (p : Pattern) : (!walkGuard soko2_2.board support p 160 159 .west || decide (bonus 160 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound623 p)
end NetHack.Sokoban22Refined85
