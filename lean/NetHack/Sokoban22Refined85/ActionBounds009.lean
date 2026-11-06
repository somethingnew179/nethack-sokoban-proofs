import NetHack.Sokoban22Refined85.ActionBounds008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard216 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 95 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound216 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 95 .east = true) : bonus 94 p ≤ bonus 95 p := by
  have certified := compare19 p (guard216 p guard)
  simpa only [at94, at95, Int.zero_add] using certified
theorem check216 (p : Pattern) : (!walkGuard soko2_2.board support p 94 95 .east || decide (bonus 94 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound216 p)
theorem guard217 (p : Pattern) (guard : pushGuard support p 94 95 96 96 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound217 (p : Pattern) (guard : pushGuard support p 94 95 96 96 = true) : bonus 94 p ≤ 1 + Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.boulder 95 + bonus 95 (change p 95 (some 96)) := by
  have certified := compare20 p (guard217 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 95 (some 96))
  have normalized := agree312 _ _ (change_representative support p 95 (some 96) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check217 (p : Pattern) : (!pushGuard support p 94 95 96 96 || decide (bonus 94 p ≤ 1 + Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.boulder 95 + bonus 95 (change p 95 (some 96)))) = true :=
  check_of_implication _ _ (bound217 p)
theorem guard218 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 93 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound218 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 93 .west = true) : bonus 94 p ≤ bonus 93 p := by
  have certified := compare19 p (guard218 p guard)
  simpa only [at94, at93, Int.zero_add] using certified
theorem check218 (p : Pattern) : (!walkGuard soko2_2.board support p 94 93 .west || decide (bonus 94 p ≤ bonus 93 p)) = true :=
  check_of_implication _ _ (bound218 p)
theorem guard219 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 73 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound219 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 73 .northEast = true) : bonus 94 p ≤ bonus 73 p := by
  have certified := compare19 p (guard219 p guard)
  simpa only [at94, at73, Int.zero_add] using certified
theorem check219 (p : Pattern) : (!walkGuard soko2_2.board support p 94 73 .northEast || decide (bonus 94 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound219 p)
theorem guard220 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 71 .northWest = true) : d4042 p = 1 := by
  change (!false && !(p 71) && !(true && true && false)) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound220 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 71 .northWest = true) : bonus 94 p ≤ bonus 71 p := by
  have certified := compare1091 p (guard220 p guard)
  simpa only [at94, at71, Int.zero_add] using certified
theorem check220 (p : Pattern) : (!walkGuard soko2_2.board support p 94 71 .northWest || decide (bonus 94 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound220 p)
theorem guard221 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 115 .southWest = true) : d4058 p = 1 := by
  change (!false && !(p 115) && !(true && (p 116) && false)) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116
  all_goals simp [d0, d1, d4058, h115, h116] at guard ⊢
theorem bound221 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 115 .southWest = true) : bonus 94 p ≤ bonus 115 p := by
  have certified := compare1113 p (guard221 p guard)
  simpa only [at94, at115, Int.zero_add] using certified
theorem check221 (p : Pattern) : (!walkGuard soko2_2.board support p 94 115 .southWest || decide (bonus 94 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound221 p)
theorem guard222 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 73 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound222 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 73 .north = true) : bonus 95 p ≤ bonus 73 p := by
  have certified := compare19 p (guard222 p guard)
  simpa only [at95, at73, Int.zero_add] using certified
theorem check222 (p : Pattern) : (!walkGuard soko2_2.board support p 95 73 .north || decide (bonus 95 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound222 p)
theorem guard223 (p : Pattern) (guard : pushGuard support p 95 73 51 51 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound223 (p : Pattern) (guard : pushGuard support p 95 73 51 51 = true) : bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder 51 - Generated.soko2_2Potential.boulder 73 + bonus 73 (change p 73 (some 51)) := by
  have certified := compare20 p (guard223 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 73 (some 51))
  have normalized := agree312 _ _ (change_representative support p 73 (some 51) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check223 (p : Pattern) : (!pushGuard support p 95 73 51 51 || decide (bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder 51 - Generated.soko2_2Potential.boulder 73 + bonus 73 (change p 73 (some 51)))) = true :=
  check_of_implication _ _ (bound223 p)
theorem guard224 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 96 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound224 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 96 .east = true) : bonus 95 p ≤ bonus 96 p := by
  have certified := compare19 p (guard224 p guard)
  simpa only [at95, at96, Int.zero_add] using certified
theorem check224 (p : Pattern) : (!walkGuard soko2_2.board support p 95 96 .east || decide (bonus 95 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound224 p)
theorem guard225 (p : Pattern) (guard : pushGuard support p 95 96 97 97 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound225 (p : Pattern) (guard : pushGuard support p 95 96 97 97 = true) : bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder 97 - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some 97)) := by
  have certified := compare20 p (guard225 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 96 (some 97))
  have normalized := agree312 _ _ (change_representative support p 96 (some 97) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check225 (p : Pattern) : (!pushGuard support p 95 96 97 97 || decide (bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder 97 - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some 97)))) = true :=
  check_of_implication _ _ (bound225 p)
theorem guard226 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 94 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound226 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 94 .west = true) : bonus 95 p ≤ bonus 94 p := by
  have certified := compare19 p (guard226 p guard)
  simpa only [at95, at94, Int.zero_add] using certified
theorem check226 (p : Pattern) : (!walkGuard soko2_2.board support p 95 94 .west || decide (bonus 95 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound226 p)
theorem guard227 (p : Pattern) (guard : pushGuard support p 95 94 93 93 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound227 (p : Pattern) (guard : pushGuard support p 95 94 93 93 = true) : bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder 93 - Generated.soko2_2Potential.boulder 94 + bonus 94 (change p 94 (some 93)) := by
  have certified := compare19 p (guard227 p guard)
  change d312 p ≤ (0 : Int) + d312 (change p 94 (some 93))
  have normalized := agree312 _ _ (change_representative support p 94 (some 93) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (0 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check227 (p : Pattern) : (!pushGuard support p 95 94 93 93 || decide (bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder 93 - Generated.soko2_2Potential.boulder 94 + bonus 94 (change p 94 (some 93)))) = true :=
  check_of_implication _ _ (bound227 p)
theorem guard228 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 74 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound228 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 74 .northEast = true) : bonus 95 p ≤ bonus 74 p := by
  have certified := compare19 p (guard228 p guard)
  simpa only [at95, at74, Int.zero_add] using certified
theorem check228 (p : Pattern) : (!walkGuard soko2_2.board support p 95 74 .northEast || decide (bonus 95 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound228 p)
theorem guard229 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 118 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound229 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 118 .southEast = true) : bonus 95 p ≤ bonus 118 p := by
  have certified := compare19 p (guard229 p guard)
  simpa only [at95, at118, Int.zero_add] using certified
theorem check229 (p : Pattern) : (!walkGuard soko2_2.board support p 95 118 .southEast || decide (bonus 95 p ≤ bonus 118 p)) = true :=
  check_of_implication _ _ (bound229 p)
theorem guard230 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 116 .southWest = true) : d4066 p = 1 := by
  change (!false && !(p 116) && !(true && true && false)) = true at guard
  cases h116 : p 116
  all_goals simp [d0, d1, d4066, h116] at guard ⊢
theorem bound230 (p : Pattern) (guard : walkGuard soko2_2.board support p 95 116 .southWest = true) : bonus 95 p ≤ bonus 116 p := by
  have certified := compare1147 p (guard230 p guard)
  simpa only [at95, at116, Int.zero_add] using certified
theorem check230 (p : Pattern) : (!walkGuard soko2_2.board support p 95 116 .southWest || decide (bonus 95 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound230 p)
theorem guard231 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 74 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound231 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 74 .north = true) : bonus 96 p ≤ bonus 74 p := by
  have certified := compare19 p (guard231 p guard)
  simpa only [at96, at74, Int.zero_add] using certified
theorem check231 (p : Pattern) : (!walkGuard soko2_2.board support p 96 74 .north || decide (bonus 96 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound231 p)
theorem guard232 (p : Pattern) (guard : pushGuard support p 96 74 52 52 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound232 (p : Pattern) (guard : pushGuard support p 96 74 52 52 = true) : bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder 52 - Generated.soko2_2Potential.boulder 74 + bonus 74 (change p 74 (some 52)) := by
  have certified := compare20 p (guard232 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 74 (some 52))
  have normalized := agree312 _ _ (change_representative support p 74 (some 52) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check232 (p : Pattern) : (!pushGuard support p 96 74 52 52 || decide (bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder 52 - Generated.soko2_2Potential.boulder 74 + bonus 74 (change p 74 (some 52)))) = true :=
  check_of_implication _ _ (bound232 p)
theorem guard233 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 118 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound233 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 118 .south = true) : bonus 96 p ≤ bonus 118 p := by
  have certified := compare19 p (guard233 p guard)
  simpa only [at96, at118, Int.zero_add] using certified
theorem check233 (p : Pattern) : (!walkGuard soko2_2.board support p 96 118 .south || decide (bonus 96 p ≤ bonus 118 p)) = true :=
  check_of_implication _ _ (bound233 p)
theorem guard234 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 97 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound234 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 97 .east = true) : bonus 96 p ≤ bonus 97 p := by
  have certified := compare19 p (guard234 p guard)
  simpa only [at96, at97, Int.zero_add] using certified
theorem check234 (p : Pattern) : (!walkGuard soko2_2.board support p 96 97 .east || decide (bonus 96 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound234 p)
theorem guard235 (p : Pattern) (guard : pushGuard support p 96 97 98 98 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound235 (p : Pattern) (guard : pushGuard support p 96 97 98 98 = true) : bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder 98 - Generated.soko2_2Potential.boulder 97 + bonus 97 (change p 97 (some 98)) := by
  have certified := compare20 p (guard235 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 97 (some 98))
  have normalized := agree312 _ _ (change_representative support p 97 (some 98) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check235 (p : Pattern) : (!pushGuard support p 96 97 98 98 || decide (bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder 98 - Generated.soko2_2Potential.boulder 97 + bonus 97 (change p 97 (some 98)))) = true :=
  check_of_implication _ _ (bound235 p)
theorem guard236 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 95 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound236 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 95 .west = true) : bonus 96 p ≤ bonus 95 p := by
  have certified := compare19 p (guard236 p guard)
  simpa only [at96, at95, Int.zero_add] using certified
theorem check236 (p : Pattern) : (!walkGuard soko2_2.board support p 96 95 .west || decide (bonus 96 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound236 p)
theorem guard237 (p : Pattern) (guard : pushGuard support p 96 95 94 94 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound237 (p : Pattern) (guard : pushGuard support p 96 95 94 94 = true) : bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder 94 - Generated.soko2_2Potential.boulder 95 + bonus 95 (change p 95 (some 94)) := by
  have certified := compare19 p (guard237 p guard)
  change d312 p ≤ (0 : Int) + d312 (change p 95 (some 94))
  have normalized := agree312 _ _ (change_representative support p 95 (some 94) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (0 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check237 (p : Pattern) : (!pushGuard support p 96 95 94 94 || decide (bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder 94 - Generated.soko2_2Potential.boulder 95 + bonus 95 (change p 95 (some 94)))) = true :=
  check_of_implication _ _ (bound237 p)
theorem guard238 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 73 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound238 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 73 .northWest = true) : bonus 96 p ≤ bonus 73 p := by
  have certified := compare19 p (guard238 p guard)
  simpa only [at96, at73, Int.zero_add] using certified
theorem check238 (p : Pattern) : (!walkGuard soko2_2.board support p 96 73 .northWest || decide (bonus 96 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound238 p)
theorem guard239 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 119 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound239 (p : Pattern) (guard : walkGuard soko2_2.board support p 96 119 .southEast = true) : bonus 96 p ≤ bonus 119 p := by
  have certified := compare19 p (guard239 p guard)
  simpa only [at96, at119, Int.zero_add] using certified
theorem check239 (p : Pattern) : (!walkGuard soko2_2.board support p 96 119 .southEast || decide (bonus 96 p ≤ bonus 119 p)) = true :=
  check_of_implication _ _ (bound239 p)
end NetHack.Sokoban22Refined85
