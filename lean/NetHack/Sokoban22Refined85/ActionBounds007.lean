import NetHack.Sokoban22Refined85.ActionBounds006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard168 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 83 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound168 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 83 .east = true) : bonus 82 p ≤ bonus 83 p := by
  have certified := compare1086 p (guard168 p guard)
  simpa only [at82, at83, Int.zero_add] using certified
theorem check168 (p : Pattern) : (!walkGuard soko2_2.board support p 82 83 .east || decide (bonus 82 p ≤ bonus 83 p)) = true :=
  check_of_implication _ _ (bound168 p)
theorem guard169 (p : Pattern) (guard : pushGuard support p 82 83 84 84 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound169 (p : Pattern) (guard : pushGuard support p 82 83 84 84 = true) : bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder 84 - Generated.soko2_2Potential.boulder 83 + bonus 83 (change p 83 (some 84)) := by
  have certified := compare1087 p (guard169 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 83 (some 84))
  have normalized := agree0 _ _ (change_representative support p 83 (some 84) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check169 (p : Pattern) : (!pushGuard support p 82 83 84 84 || decide (bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder 84 - Generated.soko2_2Potential.boulder 83 + bonus 83 (change p 83 (some 84)))) = true :=
  check_of_implication _ _ (bound169 p)
theorem guard170 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 81 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound170 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 81 .west = true) : bonus 82 p ≤ bonus 81 p := by
  have certified := compare1086 p (guard170 p guard)
  simpa only [at82, at81, Int.zero_add] using certified
theorem check170 (p : Pattern) : (!walkGuard soko2_2.board support p 82 81 .west || decide (bonus 82 p ≤ bonus 81 p)) = true :=
  check_of_implication _ _ (bound170 p)
theorem guard171 (p : Pattern) (guard : pushGuard support p 82 81 80 80 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound171 (p : Pattern) (guard : pushGuard support p 82 81 80 80 = true) : bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder 80 - Generated.soko2_2Potential.boulder 81 + bonus 81 (change p 81 (some 80)) := by
  have certified := compare1087 p (guard171 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 81 (some 80))
  have normalized := agree0 _ _ (change_representative support p 81 (some 80) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check171 (p : Pattern) : (!pushGuard support p 82 81 80 80 || decide (bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder 80 - Generated.soko2_2Potential.boulder 81 + bonus 81 (change p 81 (some 80)))) = true :=
  check_of_implication _ _ (bound171 p)
theorem guard172 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 105 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound172 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 105 .southEast = true) : bonus 82 p ≤ bonus 105 p := by
  have certified := compare1086 p (guard172 p guard)
  simpa only [at82, at105, Int.zero_add] using certified
theorem check172 (p : Pattern) : (!walkGuard soko2_2.board support p 82 105 .southEast || decide (bonus 82 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound172 p)
theorem guard173 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 103 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound173 (p : Pattern) (guard : walkGuard soko2_2.board support p 82 103 .southWest = true) : bonus 82 p ≤ bonus 103 p := by
  have certified := compare1086 p (guard173 p guard)
  simpa only [at82, at103, Int.zero_add] using certified
theorem check173 (p : Pattern) : (!walkGuard soko2_2.board support p 82 103 .southWest || decide (bonus 82 p ≤ bonus 103 p)) = true :=
  check_of_implication _ _ (bound173 p)
theorem guard174 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 105 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound174 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 105 .south = true) : bonus 83 p ≤ bonus 105 p := by
  have certified := compare1086 p (guard174 p guard)
  simpa only [at83, at105, Int.zero_add] using certified
theorem check174 (p : Pattern) : (!walkGuard soko2_2.board support p 83 105 .south || decide (bonus 83 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound174 p)
theorem guard175 (p : Pattern) (guard : pushGuard support p 83 105 127 127 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound175 (p : Pattern) (guard : pushGuard support p 83 105 127 127 = true) : bonus 83 p ≤ 1 + Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some 127)) := by
  have certified := compare1087 p (guard175 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 105 (some 127))
  have normalized := agree0 _ _ (change_representative support p 105 (some 127) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check175 (p : Pattern) : (!pushGuard support p 83 105 127 127 || decide (bonus 83 p ≤ 1 + Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some 127)))) = true :=
  check_of_implication _ _ (bound175 p)
theorem guard176 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 84 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound176 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 84 .east = true) : bonus 83 p ≤ bonus 84 p := by
  have certified := compare1086 p (guard176 p guard)
  simpa only [at83, at84, Int.zero_add] using certified
theorem check176 (p : Pattern) : (!walkGuard soko2_2.board support p 83 84 .east || decide (bonus 83 p ≤ bonus 84 p)) = true :=
  check_of_implication _ _ (bound176 p)
theorem guard177 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 82 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound177 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 82 .west = true) : bonus 83 p ≤ bonus 82 p := by
  have certified := compare1086 p (guard177 p guard)
  simpa only [at83, at82, Int.zero_add] using certified
theorem check177 (p : Pattern) : (!walkGuard soko2_2.board support p 83 82 .west || decide (bonus 83 p ≤ bonus 82 p)) = true :=
  check_of_implication _ _ (bound177 p)
theorem guard178 (p : Pattern) (guard : pushGuard support p 83 82 81 81 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound178 (p : Pattern) (guard : pushGuard support p 83 82 81 81 = true) : bonus 83 p ≤ 1 + Generated.soko2_2Potential.boulder 81 - Generated.soko2_2Potential.boulder 82 + bonus 82 (change p 82 (some 81)) := by
  have certified := compare1087 p (guard178 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 82 (some 81))
  have normalized := agree0 _ _ (change_representative support p 82 (some 81) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check178 (p : Pattern) : (!pushGuard support p 83 82 81 81 || decide (bonus 83 p ≤ 1 + Generated.soko2_2Potential.boulder 81 - Generated.soko2_2Potential.boulder 82 + bonus 82 (change p 82 (some 81)))) = true :=
  check_of_implication _ _ (bound178 p)
theorem guard179 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 106 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound179 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 106 .southEast = true) : bonus 83 p ≤ bonus 106 p := by
  have certified := compare1086 p (guard179 p guard)
  simpa only [at83, at106, Int.zero_add] using certified
theorem check179 (p : Pattern) : (!walkGuard soko2_2.board support p 83 106 .southEast || decide (bonus 83 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound179 p)
theorem guard180 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 104 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound180 (p : Pattern) (guard : walkGuard soko2_2.board support p 83 104 .southWest = true) : bonus 83 p ≤ bonus 104 p := by
  have certified := compare1086 p (guard180 p guard)
  simpa only [at83, at104, Int.zero_add] using certified
theorem check180 (p : Pattern) : (!walkGuard soko2_2.board support p 83 104 .southWest || decide (bonus 83 p ≤ bonus 104 p)) = true :=
  check_of_implication _ _ (bound180 p)
theorem guard181 (p : Pattern) (guard : walkGuard soko2_2.board support p 84 106 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound181 (p : Pattern) (guard : walkGuard soko2_2.board support p 84 106 .south = true) : bonus 84 p ≤ bonus 106 p := by
  have certified := compare1086 p (guard181 p guard)
  simpa only [at84, at106, Int.zero_add] using certified
theorem check181 (p : Pattern) : (!walkGuard soko2_2.board support p 84 106 .south || decide (bonus 84 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound181 p)
theorem guard182 (p : Pattern) (guard : pushGuard support p 84 106 128 128 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound182 (p : Pattern) (guard : pushGuard support p 84 106 128 128 = true) : bonus 84 p ≤ 1 + Generated.soko2_2Potential.boulder 128 - Generated.soko2_2Potential.boulder 106 + bonus 106 (change p 106 (some 128)) := by
  have certified := compare1087 p (guard182 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 106 (some 128))
  have normalized := agree0 _ _ (change_representative support p 106 (some 128) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check182 (p : Pattern) : (!pushGuard support p 84 106 128 128 || decide (bonus 84 p ≤ 1 + Generated.soko2_2Potential.boulder 128 - Generated.soko2_2Potential.boulder 106 + bonus 106 (change p 106 (some 128)))) = true :=
  check_of_implication _ _ (bound182 p)
theorem guard183 (p : Pattern) (guard : walkGuard soko2_2.board support p 84 83 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound183 (p : Pattern) (guard : walkGuard soko2_2.board support p 84 83 .west = true) : bonus 84 p ≤ bonus 83 p := by
  have certified := compare1086 p (guard183 p guard)
  simpa only [at84, at83, Int.zero_add] using certified
theorem check183 (p : Pattern) : (!walkGuard soko2_2.board support p 84 83 .west || decide (bonus 84 p ≤ bonus 83 p)) = true :=
  check_of_implication _ _ (bound183 p)
theorem guard184 (p : Pattern) (guard : pushGuard support p 84 83 82 82 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound184 (p : Pattern) (guard : pushGuard support p 84 83 82 82 = true) : bonus 84 p ≤ 1 + Generated.soko2_2Potential.boulder 82 - Generated.soko2_2Potential.boulder 83 + bonus 83 (change p 83 (some 82)) := by
  have certified := compare1087 p (guard184 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 83 (some 82))
  have normalized := agree0 _ _ (change_representative support p 83 (some 82) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check184 (p : Pattern) : (!pushGuard support p 84 83 82 82 || decide (bonus 84 p ≤ 1 + Generated.soko2_2Potential.boulder 82 - Generated.soko2_2Potential.boulder 83 + bonus 83 (change p 83 (some 82)))) = true :=
  check_of_implication _ _ (bound184 p)
theorem guard185 (p : Pattern) (guard : walkGuard soko2_2.board support p 84 105 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound185 (p : Pattern) (guard : walkGuard soko2_2.board support p 84 105 .southWest = true) : bonus 84 p ≤ bonus 105 p := by
  have certified := compare1086 p (guard185 p guard)
  simpa only [at84, at105, Int.zero_add] using certified
theorem check185 (p : Pattern) : (!walkGuard soko2_2.board support p 84 105 .southWest || decide (bonus 84 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound185 p)
theorem guard186 (p : Pattern) (guard : walkGuard soko2_2.board support p 89 67 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound186 (p : Pattern) (guard : walkGuard soko2_2.board support p 89 67 .north = true) : bonus 89 p ≤ bonus 67 p := by
  have certified := compare0 p (guard186 p guard)
  simpa only [at89, at67, Int.zero_add] using certified
theorem check186 (p : Pattern) : (!walkGuard soko2_2.board support p 89 67 .north || decide (bonus 89 p ≤ bonus 67 p)) = true :=
  check_of_implication _ _ (bound186 p)
theorem guard187 (p : Pattern) (guard : pushGuard support p 89 67 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound187 (p : Pattern) (guard : pushGuard support p 89 67 45 45 = true) : bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder 45 - Generated.soko2_2Potential.boulder 67 + bonus 67 (change p 67 (some 45)) := by
  have certified := compare1 p (guard187 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 67 (some 45))
  have normalized := agree267 _ _ (change_representative support p 67 (some 45) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check187 (p : Pattern) : (!pushGuard support p 89 67 45 45 || decide (bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder 45 - Generated.soko2_2Potential.boulder 67 + bonus 67 (change p 67 (some 45)))) = true :=
  check_of_implication _ _ (bound187 p)
theorem guard188 (p : Pattern) (guard : walkGuard soko2_2.board support p 89 111 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound188 (p : Pattern) (guard : walkGuard soko2_2.board support p 89 111 .south = true) : bonus 89 p ≤ bonus 111 p := by
  have certified := compare0 p (guard188 p guard)
  simpa only [at89, at111, Int.zero_add] using certified
theorem check188 (p : Pattern) : (!walkGuard soko2_2.board support p 89 111 .south || decide (bonus 89 p ≤ bonus 111 p)) = true :=
  check_of_implication _ _ (bound188 p)
theorem guard189 (p : Pattern) (guard : pushGuard support p 89 111 133 133 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound189 (p : Pattern) (guard : pushGuard support p 89 111 133 133 = true) : bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder 133 - Generated.soko2_2Potential.boulder 111 + bonus 111 (change p 111 (some 133)) := by
  have certified := compare1 p (guard189 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 111 (some 133))
  have normalized := agree267 _ _ (change_representative support p 111 (some 133) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check189 (p : Pattern) : (!pushGuard support p 89 111 133 133 || decide (bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder 133 - Generated.soko2_2Potential.boulder 111 + bonus 111 (change p 111 (some 133)))) = true :=
  check_of_implication _ _ (bound189 p)
theorem guard190 (p : Pattern) (guard : walkGuard soko2_2.board support p 89 90 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound190 (p : Pattern) (guard : walkGuard soko2_2.board support p 89 90 .east = true) : bonus 89 p ≤ bonus 90 p := by
  have certified := compare0 p (guard190 p guard)
  simpa only [at89, at90, Int.zero_add] using certified
theorem check190 (p : Pattern) : (!walkGuard soko2_2.board support p 89 90 .east || decide (bonus 89 p ≤ bonus 90 p)) = true :=
  check_of_implication _ _ (bound190 p)
theorem guard191 (p : Pattern) (guard : pushGuard support p 89 90 91 91 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound191 (p : Pattern) (guard : pushGuard support p 89 90 91 91 = true) : bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder 91 - Generated.soko2_2Potential.boulder 90 + bonus 90 (change p 90 (some 91)) := by
  have certified := compare1 p (guard191 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 90 (some 91))
  have normalized := agree267 _ _ (change_representative support p 90 (some 91) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check191 (p : Pattern) : (!pushGuard support p 89 90 91 91 || decide (bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder 91 - Generated.soko2_2Potential.boulder 90 + bonus 90 (change p 90 (some 91)))) = true :=
  check_of_implication _ _ (bound191 p)
end NetHack.Sokoban22Refined85
