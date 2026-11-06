import NetHack.Sokoban32Refined.ActionBounds008
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard216 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 53 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound216 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 53 .north = true) : bonus 79 p ≤ bonus 53 p := by
  have certified := compare0 p (guard216 p guard)
  simpa only [at79, at53, Int.zero_add] using certified
theorem check216 (p : Pattern) : (!walkGuard soko3_2.board support p 79 53 .north || decide (bonus 79 p ≤ bonus 53 p)) = true :=
  check_of_implication _ _ (bound216 p)
theorem guard217 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 105 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound217 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 105 .south = true) : bonus 79 p ≤ bonus 105 p := by
  have certified := compare0 p (guard217 p guard)
  simpa only [at79, at105, Int.zero_add] using certified
theorem check217 (p : Pattern) : (!walkGuard soko3_2.board support p 79 105 .south || decide (bonus 79 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound217 p)
theorem guard218 (p : Pattern) (guard : pushGuard support p 79 105 131 131 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound218 (p : Pattern) (guard : pushGuard support p 79 105 131 131 = true) : bonus 79 p ≤ 1 + Generated.soko3_2Potential.boulder 131 - Generated.soko3_2Potential.boulder 105 + bonus 105 (change p 105 (some 131)) := by
  have certified := compare104 p (guard218 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 105 (some 131))
  have normalized := agree134 _ _ (change_representative support p 105 (some 131) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check218 (p : Pattern) : (!pushGuard support p 79 105 131 131 || decide (bonus 79 p ≤ 1 + Generated.soko3_2Potential.boulder 131 - Generated.soko3_2Potential.boulder 105 + bonus 105 (change p 105 (some 131)))) = true :=
  check_of_implication _ _ (bound218 p)
theorem guard219 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 80 .east = true) : d827 p = 1 := by
  change (!false && !(p 80) && !false) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound219 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 80 .east = true) : bonus 79 p ≤ bonus 80 p := by
  have certified := compare107 p (guard219 p guard)
  simpa only [at79, at80, Int.zero_add] using certified
theorem check219 (p : Pattern) : (!walkGuard soko3_2.board support p 79 80 .east || decide (bonus 79 p ≤ bonus 80 p)) = true :=
  check_of_implication _ _ (bound219 p)
theorem guard220 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 54 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 80))) = true at guard
  cases h80 : p 80
  all_goals simp [d1, h80] at guard ⊢
theorem bound220 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 54 .northEast = true) : bonus 79 p ≤ bonus 54 p := by
  have certified := compare0 p (guard220 p guard)
  simpa only [at79, at54, Int.zero_add] using certified
theorem check220 (p : Pattern) : (!walkGuard soko3_2.board support p 79 54 .northEast || decide (bonus 79 p ≤ bonus 54 p)) = true :=
  check_of_implication _ _ (bound220 p)
theorem guard221 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 106 .southEast = true) : d829 p = 1 := by
  change (!false && !(p 106) && !(true && false && (p 80))) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106
  all_goals simp [d0, d1, d829, h80, h106] at guard ⊢
theorem bound221 (p : Pattern) (guard : walkGuard soko3_2.board support p 79 106 .southEast = true) : bonus 79 p ≤ bonus 106 p := by
  have certified := compare297 p (guard221 p guard)
  simpa only [at79, at106, Int.zero_add] using certified
theorem check221 (p : Pattern) : (!walkGuard soko3_2.board support p 79 106 .southEast || decide (bonus 79 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound221 p)
theorem guard222 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 54 .north = true) : d827 p = 1 := by
  change (!(p 80) && !false && !false) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound222 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 54 .north = true) : bonus 80 p ≤ bonus 54 p := by
  have certified := compare299 p (guard222 p guard)
  simpa only [at80, at54, Int.zero_add] using certified
theorem check222 (p : Pattern) : (!walkGuard soko3_2.board support p 80 54 .north || decide (bonus 80 p ≤ bonus 54 p)) = true :=
  check_of_implication _ _ (bound222 p)
theorem guard223 (p : Pattern) (guard : pushGuard support p 80 54 28 28 = true) : d827 p = 1 := by
  change (!(p 80) && (!false || false) && !false && (!false || false)) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound223 (p : Pattern) (guard : pushGuard support p 80 54 28 28 = true) : bonus 80 p ≤ 1 + Generated.soko3_2Potential.boulder 28 - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some 28)) := by
  have certified := compare302 p (guard223 p guard)
  change d173 p ≤ (1 : Int) + d134 (change p 54 (some 28))
  have normalized := agree134 _ _ (change_representative support p 54 (some 28) 10000 dummy_outside)
  rw [normalized]
  change d173 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check223 (p : Pattern) : (!pushGuard support p 80 54 28 28 || decide (bonus 80 p ≤ 1 + Generated.soko3_2Potential.boulder 28 - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some 28)))) = true :=
  check_of_implication _ _ (bound223 p)
theorem guard224 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 106 .south = true) : d838 p = 1 := by
  change (!(p 80) && !(p 106) && !false) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106
  all_goals simp [d0, d1, d829, d838, h80, h106] at guard ⊢
theorem bound224 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 106 .south = true) : bonus 80 p ≤ bonus 106 p := by
  have certified := compare304 p (guard224 p guard)
  simpa only [at80, at106, Int.zero_add] using certified
theorem check224 (p : Pattern) : (!walkGuard soko3_2.board support p 80 106 .south || decide (bonus 80 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound224 p)
theorem guard225 (p : Pattern) (guard : pushGuard support p 80 106 132 132 = true) : d843 p = 1 := by
  change (!(p 80) && (!true || (p 106)) && !(p 132) && (!(p 132) || false)) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106 <;> cases h132 : p 132
  all_goals simp [d0, d1, d841, d842, d843, h80, h106, h132] at guard ⊢
theorem bound225 (p : Pattern) (guard : pushGuard support p 80 106 132 132 = true) : bonus 80 p ≤ 1 + Generated.soko3_2Potential.boulder 132 - Generated.soko3_2Potential.boulder 106 + bonus 106 (change p 106 (some 132)) := by
  have certified := compare412 p (guard225 p guard)
  change d173 p ≤ (1 : Int) + d183 (change p 106 (some 132))
  have normalized := agree183 _ _ (change_representative support p 106 (some 132) 10000 dummy_outside)
  rw [normalized]
  change d173 p ≤ (1 : Int) + d183 (change p 106 (some 132))
  rw [sub502]
  exact certified
theorem check225 (p : Pattern) : (!pushGuard support p 80 106 132 132 || decide (bonus 80 p ≤ 1 + Generated.soko3_2Potential.boulder 132 - Generated.soko3_2Potential.boulder 106 + bonus 106 (change p 106 (some 132)))) = true :=
  check_of_implication _ _ (bound225 p)
theorem guard226 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 79 .west = true) : d827 p = 1 := by
  change (!(p 80) && !false && !false) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound226 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 79 .west = true) : bonus 80 p ≤ bonus 79 p := by
  have certified := compare299 p (guard226 p guard)
  simpa only [at80, at79, Int.zero_add] using certified
theorem check226 (p : Pattern) : (!walkGuard soko3_2.board support p 80 79 .west || decide (bonus 80 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound226 p)
theorem guard227 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 55 .northEast = true) : d827 p = 1 := by
  change (!(p 80) && !false && !(true && false && true)) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound227 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 55 .northEast = true) : bonus 80 p ≤ bonus 55 p := by
  have certified := compare299 p (guard227 p guard)
  simpa only [at80, at55, Int.zero_add] using certified
theorem check227 (p : Pattern) : (!walkGuard soko3_2.board support p 80 55 .northEast || decide (bonus 80 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound227 p)
theorem guard228 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 53 .northWest = true) : d827 p = 1 := by
  change (!(p 80) && !false && !(true && false && false)) = true at guard
  cases h80 : p 80
  all_goals simp [d0, d1, d827, h80] at guard ⊢
theorem bound228 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 53 .northWest = true) : bonus 80 p ≤ bonus 53 p := by
  have certified := compare299 p (guard228 p guard)
  simpa only [at80, at53, Int.zero_add] using certified
theorem check228 (p : Pattern) : (!walkGuard soko3_2.board support p 80 53 .northWest || decide (bonus 80 p ≤ bonus 53 p)) = true :=
  check_of_implication _ _ (bound228 p)
theorem guard229 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 105 .southWest = true) : d827 p = 1 := by
  change (!(p 80) && !false && !(true && (p 106) && false)) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106
  all_goals simp [d0, d1, d827, h80, h106] at guard ⊢
theorem bound229 (p : Pattern) (guard : walkGuard soko3_2.board support p 80 105 .southWest = true) : bonus 80 p ≤ bonus 105 p := by
  have certified := compare299 p (guard229 p guard)
  simpa only [at80, at105, Int.zero_add] using certified
theorem check229 (p : Pattern) : (!walkGuard soko3_2.board support p 80 105 .southWest || decide (bonus 80 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound229 p)
theorem guard230 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 60 .north = true) : d833 p = 1 := by
  change (!(p 86) && !false && !false) = true at guard
  cases h86 : p 86
  all_goals simp [d0, d1, d833, h86] at guard ⊢
theorem bound230 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 60 .north = true) : bonus 86 p ≤ bonus 60 p := by
  have certified := compare417 p (guard230 p guard)
  simpa only [at86, at60, Int.zero_add] using certified
theorem check230 (p : Pattern) : (!walkGuard soko3_2.board support p 86 60 .north || decide (bonus 86 p ≤ bonus 60 p)) = true :=
  check_of_implication _ _ (bound230 p)
theorem guard231 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 112 .south = true) : d854 p = 1 := by
  change (!(p 86) && !(p 112) && !false) = true at guard
  cases h86 : p 86 <;> cases h112 : p 112
  all_goals simp [d0, d1, d835, d854, h86, h112] at guard ⊢
theorem bound231 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 112 .south = true) : bonus 86 p ≤ bonus 112 p := by
  have certified := compare435 p (guard231 p guard)
  simpa only [at86, at112, Int.zero_add] using certified
theorem check231 (p : Pattern) : (!walkGuard soko3_2.board support p 86 112 .south || decide (bonus 86 p ≤ bonus 112 p)) = true :=
  check_of_implication _ _ (bound231 p)
theorem guard232 (p : Pattern) (guard : pushGuard support p 86 112 138 138 = true) : d859 p = 1 := by
  change (!(p 86) && (!true || (p 112)) && !(p 138) && (!(p 138) || false)) = true at guard
  cases h86 : p 86 <;> cases h112 : p 112 <;> cases h138 : p 138
  all_goals simp [d0, d1, d857, d858, d859, h86, h112, h138] at guard ⊢
theorem bound232 (p : Pattern) (guard : pushGuard support p 86 112 138 138 = true) : bonus 86 p ≤ 1 + Generated.soko3_2Potential.boulder 138 - Generated.soko3_2Potential.boulder 112 + bonus 112 (change p 112 (some 138)) := by
  have certified := compare469 p (guard232 p guard)
  change d176 p ≤ (0 : Int) + d227 (change p 112 (some 138))
  have normalized := agree227 _ _ (change_representative support p 112 (some 138) 10000 dummy_outside)
  rw [normalized]
  change d176 p ≤ (0 : Int) + d227 (change p 112 (some 138))
  rw [sub604]
  exact certified
theorem check232 (p : Pattern) : (!pushGuard support p 86 112 138 138 || decide (bonus 86 p ≤ 1 + Generated.soko3_2Potential.boulder 138 - Generated.soko3_2Potential.boulder 112 + bonus 112 (change p 112 (some 138)))) = true :=
  check_of_implication _ _ (bound232 p)
theorem guard233 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 61 .northEast = true) : d833 p = 1 := by
  change (!(p 86) && !false && !(true && false && true)) = true at guard
  cases h86 : p 86
  all_goals simp [d0, d1, d833, h86] at guard ⊢
theorem bound233 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 61 .northEast = true) : bonus 86 p ≤ bonus 61 p := by
  have certified := compare417 p (guard233 p guard)
  simpa only [at86, at61, Int.zero_add] using certified
theorem check233 (p : Pattern) : (!walkGuard soko3_2.board support p 86 61 .northEast || decide (bonus 86 p ≤ bonus 61 p)) = true :=
  check_of_implication _ _ (bound233 p)
theorem guard234 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 59 .northWest = true) : d833 p = 1 := by
  change (!(p 86) && !false && !(true && false && true)) = true at guard
  cases h86 : p 86
  all_goals simp [d0, d1, d833, h86] at guard ⊢
theorem bound234 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 59 .northWest = true) : bonus 86 p ≤ bonus 59 p := by
  have certified := compare417 p (guard234 p guard)
  simpa only [at86, at59, Int.zero_add] using certified
theorem check234 (p : Pattern) : (!walkGuard soko3_2.board support p 86 59 .northWest || decide (bonus 86 p ≤ bonus 59 p)) = true :=
  check_of_implication _ _ (bound234 p)
theorem guard235 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 113 .southEast = true) : d869 p = 1 := by
  change (!(p 86) && !(p 113) && !(true && (p 112) && true)) = true at guard
  cases h86 : p 86 <;> cases h112 : p 112 <;> cases h113 : p 113
  all_goals simp [d0, d1, d866, d868, d869, h86, h112, h113] at guard ⊢
theorem bound235 (p : Pattern) (guard : walkGuard soko3_2.board support p 86 113 .southEast = true) : bonus 86 p ≤ bonus 113 p := by
  have certified := compare493 p (guard235 p guard)
  simpa only [at86, at113, Int.zero_add] using certified
theorem check235 (p : Pattern) : (!walkGuard soko3_2.board support p 86 113 .southEast || decide (bonus 86 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound235 p)
theorem guard236 (p : Pattern) (guard : walkGuard soko3_2.board support p 88 62 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound236 (p : Pattern) (guard : walkGuard soko3_2.board support p 88 62 .north = true) : bonus 88 p ≤ bonus 62 p := by
  have certified := compare0 p (guard236 p guard)
  simpa only [at88, at62, Int.zero_add] using certified
theorem check236 (p : Pattern) : (!walkGuard soko3_2.board support p 88 62 .north || decide (bonus 88 p ≤ bonus 62 p)) = true :=
  check_of_implication _ _ (bound236 p)
theorem guard237 (p : Pattern) (guard : walkGuard soko3_2.board support p 88 114 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound237 (p : Pattern) (guard : walkGuard soko3_2.board support p 88 114 .south = true) : bonus 88 p ≤ bonus 114 p := by
  have certified := compare0 p (guard237 p guard)
  simpa only [at88, at114, Int.zero_add] using certified
theorem check237 (p : Pattern) : (!walkGuard soko3_2.board support p 88 114 .south || decide (bonus 88 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound237 p)
theorem guard238 (p : Pattern) (guard : walkGuard soko3_2.board support p 88 61 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound238 (p : Pattern) (guard : walkGuard soko3_2.board support p 88 61 .northWest = true) : bonus 88 p ≤ bonus 61 p := by
  have certified := compare0 p (guard238 p guard)
  simpa only [at88, at61, Int.zero_add] using certified
theorem check238 (p : Pattern) : (!walkGuard soko3_2.board support p 88 61 .northWest || decide (bonus 88 p ≤ bonus 61 p)) = true :=
  check_of_implication _ _ (bound238 p)
theorem guard239 (p : Pattern) (guard : walkGuard soko3_2.board support p 88 113 .southWest = true) : d866 p = 1 := by
  change (!false && !(p 113) && !(true && false && true)) = true at guard
  cases h113 : p 113
  all_goals simp [d0, d1, d866, h113] at guard ⊢
theorem bound239 (p : Pattern) (guard : walkGuard soko3_2.board support p 88 113 .southWest = true) : bonus 88 p ≤ bonus 113 p := by
  have certified := compare535 p (guard239 p guard)
  simpa only [at88, at113, Int.zero_add] using certified
theorem check239 (p : Pattern) : (!walkGuard soko3_2.board support p 88 113 .southWest || decide (bonus 88 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound239 p)
end NetHack.Sokoban32Refined
