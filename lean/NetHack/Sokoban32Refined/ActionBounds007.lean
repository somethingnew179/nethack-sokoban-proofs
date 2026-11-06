import NetHack.Sokoban32Refined.ActionBounds006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard168 (p : Pattern) (guard : pushGuard support p 72 98 124 124 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound168 (p : Pattern) (guard : pushGuard support p 72 98 124 124 = true) : bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some 124)) := by
  have certified := compare37 p (guard168 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 98 (some 124))
  have normalized := agree0 _ _ (change_representative support p 98 (some 124) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check168 (p : Pattern) : (!pushGuard support p 72 98 124 124 || decide (bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some 124)))) = true :=
  check_of_implication _ _ (bound168 p)
theorem guard169 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 73 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound169 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 73 .east = true) : bonus 72 p ≤ bonus 73 p := by
  have certified := compare103 p (guard169 p guard)
  simpa only [at72, at73, Int.zero_add] using certified
theorem check169 (p : Pattern) : (!walkGuard soko3_2.board support p 72 73 .east || decide (bonus 72 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound169 p)
theorem guard170 (p : Pattern) (guard : pushGuard support p 72 73 74 74 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound170 (p : Pattern) (guard : pushGuard support p 72 73 74 74 = true) : bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some 74)) := by
  have certified := compare37 p (guard170 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 73 (some 74))
  have normalized := agree0 _ _ (change_representative support p 73 (some 74) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check170 (p : Pattern) : (!pushGuard support p 72 73 74 74 || decide (bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some 74)))) = true :=
  check_of_implication _ _ (bound170 p)
theorem guard171 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 71 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound171 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 71 .west = true) : bonus 72 p ≤ bonus 71 p := by
  have certified := compare103 p (guard171 p guard)
  simpa only [at72, at71, Int.zero_add] using certified
theorem check171 (p : Pattern) : (!walkGuard soko3_2.board support p 72 71 .west || decide (bonus 72 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound171 p)
theorem guard172 (p : Pattern) (guard : pushGuard support p 72 71 70 70 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound172 (p : Pattern) (guard : pushGuard support p 72 71 70 70 = true) : bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some 70)) := by
  have certified := compare37 p (guard172 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 71 (some 70))
  have normalized := agree0 _ _ (change_representative support p 71 (some 70) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check172 (p : Pattern) : (!pushGuard support p 72 71 70 70 || decide (bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some 70)))) = true :=
  check_of_implication _ _ (bound172 p)
theorem guard173 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 47 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound173 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 47 .northEast = true) : bonus 72 p ≤ bonus 47 p := by
  have certified := compare103 p (guard173 p guard)
  simpa only [at72, at47, Int.zero_add] using certified
theorem check173 (p : Pattern) : (!walkGuard soko3_2.board support p 72 47 .northEast || decide (bonus 72 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound173 p)
theorem guard174 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 45 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound174 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 45 .northWest = true) : bonus 72 p ≤ bonus 45 p := by
  have certified := compare103 p (guard174 p guard)
  simpa only [at72, at45, Int.zero_add] using certified
theorem check174 (p : Pattern) : (!walkGuard soko3_2.board support p 72 45 .northWest || decide (bonus 72 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound174 p)
theorem guard175 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 99 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound175 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 99 .southEast = true) : bonus 72 p ≤ bonus 99 p := by
  have certified := compare103 p (guard175 p guard)
  simpa only [at72, at99, Int.zero_add] using certified
theorem check175 (p : Pattern) : (!walkGuard soko3_2.board support p 72 99 .southEast || decide (bonus 72 p ≤ bonus 99 p)) = true :=
  check_of_implication _ _ (bound175 p)
theorem guard176 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 97 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound176 (p : Pattern) (guard : walkGuard soko3_2.board support p 72 97 .southWest = true) : bonus 72 p ≤ bonus 97 p := by
  have certified := compare103 p (guard176 p guard)
  simpa only [at72, at97, Int.zero_add] using certified
theorem check176 (p : Pattern) : (!walkGuard soko3_2.board support p 72 97 .southWest || decide (bonus 72 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound176 p)
theorem guard177 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 47 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound177 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 47 .north = true) : bonus 73 p ≤ bonus 47 p := by
  have certified := compare103 p (guard177 p guard)
  simpa only [at73, at47, Int.zero_add] using certified
theorem check177 (p : Pattern) : (!walkGuard soko3_2.board support p 73 47 .north || decide (bonus 73 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound177 p)
theorem guard178 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 99 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound178 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 99 .south = true) : bonus 73 p ≤ bonus 99 p := by
  have certified := compare103 p (guard178 p guard)
  simpa only [at73, at99, Int.zero_add] using certified
theorem check178 (p : Pattern) : (!walkGuard soko3_2.board support p 73 99 .south || decide (bonus 73 p ≤ bonus 99 p)) = true :=
  check_of_implication _ _ (bound178 p)
theorem guard179 (p : Pattern) (guard : pushGuard support p 73 99 125 125 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound179 (p : Pattern) (guard : pushGuard support p 73 99 125 125 = true) : bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some 125)) := by
  have certified := compare37 p (guard179 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 99 (some 125))
  have normalized := agree0 _ _ (change_representative support p 99 (some 125) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check179 (p : Pattern) : (!pushGuard support p 73 99 125 125 || decide (bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some 125)))) = true :=
  check_of_implication _ _ (bound179 p)
theorem guard180 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 74 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound180 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 74 .east = true) : bonus 73 p ≤ bonus 74 p := by
  have certified := compare103 p (guard180 p guard)
  simpa only [at73, at74, Int.zero_add] using certified
theorem check180 (p : Pattern) : (!walkGuard soko3_2.board support p 73 74 .east || decide (bonus 73 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound180 p)
theorem guard181 (p : Pattern) (guard : pushGuard support p 73 74 75 75 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound181 (p : Pattern) (guard : pushGuard support p 73 74 75 75 = true) : bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder 75 - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some 75)) := by
  have certified := compare37 p (guard181 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 74 (some 75))
  have normalized := agree0 _ _ (change_representative support p 74 (some 75) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check181 (p : Pattern) : (!pushGuard support p 73 74 75 75 || decide (bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder 75 - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some 75)))) = true :=
  check_of_implication _ _ (bound181 p)
theorem guard182 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 72 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound182 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 72 .west = true) : bonus 73 p ≤ bonus 72 p := by
  have certified := compare103 p (guard182 p guard)
  simpa only [at73, at72, Int.zero_add] using certified
theorem check182 (p : Pattern) : (!walkGuard soko3_2.board support p 73 72 .west || decide (bonus 73 p ≤ bonus 72 p)) = true :=
  check_of_implication _ _ (bound182 p)
theorem guard183 (p : Pattern) (guard : pushGuard support p 73 72 71 71 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound183 (p : Pattern) (guard : pushGuard support p 73 72 71 71 = true) : bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some 71)) := by
  have certified := compare37 p (guard183 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 72 (some 71))
  have normalized := agree0 _ _ (change_representative support p 72 (some 71) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check183 (p : Pattern) : (!pushGuard support p 73 72 71 71 || decide (bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some 71)))) = true :=
  check_of_implication _ _ (bound183 p)
theorem guard184 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 48 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound184 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 48 .northEast = true) : bonus 73 p ≤ bonus 48 p := by
  have certified := compare103 p (guard184 p guard)
  simpa only [at73, at48, Int.zero_add] using certified
theorem check184 (p : Pattern) : (!walkGuard soko3_2.board support p 73 48 .northEast || decide (bonus 73 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound184 p)
theorem guard185 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 46 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound185 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 46 .northWest = true) : bonus 73 p ≤ bonus 46 p := by
  have certified := compare103 p (guard185 p guard)
  simpa only [at73, at46, Int.zero_add] using certified
theorem check185 (p : Pattern) : (!walkGuard soko3_2.board support p 73 46 .northWest || decide (bonus 73 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound185 p)
theorem guard186 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 100 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound186 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 100 .southEast = true) : bonus 73 p ≤ bonus 100 p := by
  have certified := compare103 p (guard186 p guard)
  simpa only [at73, at100, Int.zero_add] using certified
theorem check186 (p : Pattern) : (!walkGuard soko3_2.board support p 73 100 .southEast || decide (bonus 73 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound186 p)
theorem guard187 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 98 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound187 (p : Pattern) (guard : walkGuard soko3_2.board support p 73 98 .southWest = true) : bonus 73 p ≤ bonus 98 p := by
  have certified := compare103 p (guard187 p guard)
  simpa only [at73, at98, Int.zero_add] using certified
theorem check187 (p : Pattern) : (!walkGuard soko3_2.board support p 73 98 .southWest || decide (bonus 73 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound187 p)
theorem guard188 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 48 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound188 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 48 .north = true) : bonus 74 p ≤ bonus 48 p := by
  have certified := compare103 p (guard188 p guard)
  simpa only [at74, at48, Int.zero_add] using certified
theorem check188 (p : Pattern) : (!walkGuard soko3_2.board support p 74 48 .north || decide (bonus 74 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound188 p)
theorem guard189 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 100 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound189 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 100 .south = true) : bonus 74 p ≤ bonus 100 p := by
  have certified := compare103 p (guard189 p guard)
  simpa only [at74, at100, Int.zero_add] using certified
theorem check189 (p : Pattern) : (!walkGuard soko3_2.board support p 74 100 .south || decide (bonus 74 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound189 p)
theorem guard190 (p : Pattern) (guard : pushGuard support p 74 100 126 126 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound190 (p : Pattern) (guard : pushGuard support p 74 100 126 126 = true) : bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some 126)) := by
  have certified := compare37 p (guard190 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 100 (some 126))
  have normalized := agree0 _ _ (change_representative support p 100 (some 126) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check190 (p : Pattern) : (!pushGuard support p 74 100 126 126 || decide (bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some 126)))) = true :=
  check_of_implication _ _ (bound190 p)
theorem guard191 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 75 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound191 (p : Pattern) (guard : walkGuard soko3_2.board support p 74 75 .east = true) : bonus 74 p ≤ bonus 75 p := by
  have certified := compare103 p (guard191 p guard)
  simpa only [at74, at75, Int.zero_add] using certified
theorem check191 (p : Pattern) : (!walkGuard soko3_2.board support p 74 75 .east || decide (bonus 74 p ≤ bonus 75 p)) = true :=
  check_of_implication _ _ (bound191 p)
end NetHack.Sokoban32Refined
