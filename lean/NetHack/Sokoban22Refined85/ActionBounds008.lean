import NetHack.Sokoban22Refined85.ActionBounds007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard192 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 91 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound192 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 91 .east = true) : bonus 90 p ≤ bonus 91 p := by
  have certified := compare0 p (guard192 p guard)
  simpa only [at90, at91, Int.zero_add] using certified
theorem check192 (p : Pattern) : (!walkGuard soko2_2.board support p 90 91 .east || decide (bonus 90 p ≤ bonus 91 p)) = true :=
  check_of_implication _ _ (bound192 p)
theorem guard193 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 89 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound193 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 89 .west = true) : bonus 90 p ≤ bonus 89 p := by
  have certified := compare0 p (guard193 p guard)
  simpa only [at90, at89, Int.zero_add] using certified
theorem check193 (p : Pattern) : (!walkGuard soko2_2.board support p 90 89 .west || decide (bonus 90 p ≤ bonus 89 p)) = true :=
  check_of_implication _ _ (bound193 p)
theorem guard194 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 69 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound194 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 69 .northEast = true) : bonus 90 p ≤ bonus 69 p := by
  have certified := compare0 p (guard194 p guard)
  simpa only [at90, at69, Int.zero_add] using certified
theorem check194 (p : Pattern) : (!walkGuard soko2_2.board support p 90 69 .northEast || decide (bonus 90 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound194 p)
theorem guard195 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 67 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound195 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 67 .northWest = true) : bonus 90 p ≤ bonus 67 p := by
  have certified := compare0 p (guard195 p guard)
  simpa only [at90, at67, Int.zero_add] using certified
theorem check195 (p : Pattern) : (!walkGuard soko2_2.board support p 90 67 .northWest || decide (bonus 90 p ≤ bonus 67 p)) = true :=
  check_of_implication _ _ (bound195 p)
theorem guard196 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 113 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound196 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 113 .southEast = true) : bonus 90 p ≤ bonus 113 p := by
  have certified := compare0 p (guard196 p guard)
  simpa only [at90, at113, Int.zero_add] using certified
theorem check196 (p : Pattern) : (!walkGuard soko2_2.board support p 90 113 .southEast || decide (bonus 90 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound196 p)
theorem guard197 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 111 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound197 (p : Pattern) (guard : walkGuard soko2_2.board support p 90 111 .southWest = true) : bonus 90 p ≤ bonus 111 p := by
  have certified := compare0 p (guard197 p guard)
  simpa only [at90, at111, Int.zero_add] using certified
theorem check197 (p : Pattern) : (!walkGuard soko2_2.board support p 90 111 .southWest || decide (bonus 90 p ≤ bonus 111 p)) = true :=
  check_of_implication _ _ (bound197 p)
theorem guard198 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 69 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound198 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 69 .north = true) : bonus 91 p ≤ bonus 69 p := by
  have certified := compare0 p (guard198 p guard)
  simpa only [at91, at69, Int.zero_add] using certified
theorem check198 (p : Pattern) : (!walkGuard soko2_2.board support p 91 69 .north || decide (bonus 91 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound198 p)
theorem guard199 (p : Pattern) (guard : pushGuard support p 91 69 47 47 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound199 (p : Pattern) (guard : pushGuard support p 91 69 47 47 = true) : bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.boulder 69 + bonus 69 (change p 69 (some 47)) := by
  have certified := compare1 p (guard199 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 69 (some 47))
  have normalized := agree267 _ _ (change_representative support p 69 (some 47) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check199 (p : Pattern) : (!pushGuard support p 91 69 47 47 || decide (bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.boulder 69 + bonus 69 (change p 69 (some 47)))) = true :=
  check_of_implication _ _ (bound199 p)
theorem guard200 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 113 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound200 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 113 .south = true) : bonus 91 p ≤ bonus 113 p := by
  have certified := compare0 p (guard200 p guard)
  simpa only [at91, at113, Int.zero_add] using certified
theorem check200 (p : Pattern) : (!walkGuard soko2_2.board support p 91 113 .south || decide (bonus 91 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound200 p)
theorem guard201 (p : Pattern) (guard : pushGuard support p 91 113 135 135 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound201 (p : Pattern) (guard : pushGuard support p 91 113 135 135 = true) : bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder 135 - Generated.soko2_2Potential.boulder 113 + bonus 113 (change p 113 (some 135)) := by
  have certified := compare0 p (guard201 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 113 (some 135))
  have normalized := agree267 _ _ (change_representative support p 113 (some 135) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check201 (p : Pattern) : (!pushGuard support p 91 113 135 135 || decide (bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder 135 - Generated.soko2_2Potential.boulder 113 + bonus 113 (change p 113 (some 135)))) = true :=
  check_of_implication _ _ (bound201 p)
theorem guard202 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 90 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound202 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 90 .west = true) : bonus 91 p ≤ bonus 90 p := by
  have certified := compare0 p (guard202 p guard)
  simpa only [at91, at90, Int.zero_add] using certified
theorem check202 (p : Pattern) : (!walkGuard soko2_2.board support p 91 90 .west || decide (bonus 91 p ≤ bonus 90 p)) = true :=
  check_of_implication _ _ (bound202 p)
theorem guard203 (p : Pattern) (guard : pushGuard support p 91 90 89 89 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound203 (p : Pattern) (guard : pushGuard support p 91 90 89 89 = true) : bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder 89 - Generated.soko2_2Potential.boulder 90 + bonus 90 (change p 90 (some 89)) := by
  have certified := compare1 p (guard203 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 90 (some 89))
  have normalized := agree267 _ _ (change_representative support p 90 (some 89) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check203 (p : Pattern) : (!pushGuard support p 91 90 89 89 || decide (bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder 89 - Generated.soko2_2Potential.boulder 90 + bonus 90 (change p 90 (some 89)))) = true :=
  check_of_implication _ _ (bound203 p)
theorem guard204 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 70 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound204 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 70 .northEast = true) : bonus 91 p ≤ bonus 70 p := by
  have certified := compare0 p (guard204 p guard)
  simpa only [at91, at70, Int.zero_add] using certified
theorem check204 (p : Pattern) : (!walkGuard soko2_2.board support p 91 70 .northEast || decide (bonus 91 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound204 p)
theorem guard205 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 114 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound205 (p : Pattern) (guard : walkGuard soko2_2.board support p 91 114 .southEast = true) : bonus 91 p ≤ bonus 114 p := by
  have certified := compare0 p (guard205 p guard)
  simpa only [at91, at114, Int.zero_add] using certified
theorem check205 (p : Pattern) : (!walkGuard soko2_2.board support p 91 114 .southEast || decide (bonus 91 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound205 p)
theorem guard206 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 71 .north = true) : d4042 p = 1 := by
  change (!false && !(p 71) && !false) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound206 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 71 .north = true) : bonus 93 p ≤ bonus 71 p := by
  have certified := compare1091 p (guard206 p guard)
  simpa only [at93, at71, Int.zero_add] using certified
theorem check206 (p : Pattern) : (!walkGuard soko2_2.board support p 93 71 .north || decide (bonus 93 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound206 p)
theorem guard207 (p : Pattern) (guard : pushGuard support p 93 71 49 49 = true) : d4049 p = 1 := by
  change (!false && (!true || (p 71)) && !(p 49) && (!(p 49) || false)) = true at guard
  cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4041, d4049, h49, h71] at guard ⊢
theorem bound207 (p : Pattern) (guard : pushGuard support p 93 71 49 49 = true) : bonus 93 p ≤ 1 + Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.boulder 71 + bonus 71 (change p 71 (some 49)) := by
  have certified := compare1097 p (guard207 p guard)
  change d312 p ≤ (2 : Int) + d488 (change p 71 (some 49))
  have normalized := agree488 _ _ (change_representative support p 71 (some 49) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (2 : Int) + d488 (change p 71 (some 49))
  rw [sub2100]
  exact certified
theorem check207 (p : Pattern) : (!pushGuard support p 93 71 49 49 || decide (bonus 93 p ≤ 1 + Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.boulder 71 + bonus 71 (change p 71 (some 49)))) = true :=
  check_of_implication _ _ (bound207 p)
theorem guard208 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 115 .south = true) : d4058 p = 1 := by
  change (!false && !(p 115) && !false) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound208 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 115 .south = true) : bonus 93 p ≤ bonus 115 p := by
  have certified := compare1113 p (guard208 p guard)
  simpa only [at93, at115, Int.zero_add] using certified
theorem check208 (p : Pattern) : (!walkGuard soko2_2.board support p 93 115 .south || decide (bonus 93 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound208 p)
theorem guard209 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 94 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound209 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 94 .east = true) : bonus 93 p ≤ bonus 94 p := by
  have certified := compare19 p (guard209 p guard)
  simpa only [at93, at94, Int.zero_add] using certified
theorem check209 (p : Pattern) : (!walkGuard soko2_2.board support p 93 94 .east || decide (bonus 93 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound209 p)
theorem guard210 (p : Pattern) (guard : pushGuard support p 93 94 95 95 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound210 (p : Pattern) (guard : pushGuard support p 93 94 95 95 = true) : bonus 93 p ≤ 1 + Generated.soko2_2Potential.boulder 95 - Generated.soko2_2Potential.boulder 94 + bonus 94 (change p 94 (some 95)) := by
  have certified := compare1114 p (guard210 p guard)
  change d312 p ≤ (2 : Int) + d312 (change p 94 (some 95))
  have normalized := agree312 _ _ (change_representative support p 94 (some 95) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (2 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check210 (p : Pattern) : (!pushGuard support p 93 94 95 95 || decide (bonus 93 p ≤ 1 + Generated.soko2_2Potential.boulder 95 - Generated.soko2_2Potential.boulder 94 + bonus 94 (change p 94 (some 95)))) = true :=
  check_of_implication _ _ (bound210 p)
theorem guard211 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 70 .northWest = true) : d4042 p = 1 := by
  change (!false && !false && !(true && (p 71) && true)) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound211 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 70 .northWest = true) : bonus 93 p ≤ bonus 70 p := by
  have certified := compare1118 p (guard211 p guard)
  simpa only [at93, at70, Int.zero_add] using certified
theorem check211 (p : Pattern) : (!walkGuard soko2_2.board support p 93 70 .northWest || decide (bonus 93 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound211 p)
theorem guard212 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 116 .southEast = true) : d4066 p = 1 := by
  change (!false && !(p 116) && !(true && (p 115) && false)) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116
  all_goals simp [d0, d1, d4066, h115, h116] at guard ⊢
theorem bound212 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 116 .southEast = true) : bonus 93 p ≤ bonus 116 p := by
  have certified := compare1147 p (guard212 p guard)
  simpa only [at93, at116, Int.zero_add] using certified
theorem check212 (p : Pattern) : (!walkGuard soko2_2.board support p 93 116 .southEast || decide (bonus 93 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound212 p)
theorem guard213 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 114 .southWest = true) : d4058 p = 1 := by
  change (!false && !false && !(true && (p 115) && true)) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound213 (p : Pattern) (guard : walkGuard soko2_2.board support p 93 114 .southWest = true) : bonus 93 p ≤ bonus 114 p := by
  have certified := compare1157 p (guard213 p guard)
  simpa only [at93, at114, Int.zero_add] using certified
theorem check213 (p : Pattern) : (!walkGuard soko2_2.board support p 93 114 .southWest || decide (bonus 93 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound213 p)
theorem guard214 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 116 .south = true) : d4066 p = 1 := by
  change (!false && !(p 116) && !false) = true at guard
  cases h116 : p 116
  all_goals simp [d0, d1, d4066, h116] at guard ⊢
theorem bound214 (p : Pattern) (guard : walkGuard soko2_2.board support p 94 116 .south = true) : bonus 94 p ≤ bonus 116 p := by
  have certified := compare1147 p (guard214 p guard)
  simpa only [at94, at116, Int.zero_add] using certified
theorem check214 (p : Pattern) : (!walkGuard soko2_2.board support p 94 116 .south || decide (bonus 94 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound214 p)
theorem guard215 (p : Pattern) (guard : pushGuard support p 94 116 138 138 = true) : d4069 p = 1 := by
  change (!false && (!true || (p 116)) && !(p 138) && (!(p 138) || false)) = true at guard
  cases h116 : p 116 <;> cases h138 : p 138
  all_goals simp [d0, d1, d4068, d4069, h116, h138] at guard ⊢
theorem bound215 (p : Pattern) (guard : pushGuard support p 94 116 138 138 = true) : bonus 94 p ≤ 1 + Generated.soko2_2Potential.boulder 138 - Generated.soko2_2Potential.boulder 116 + bonus 116 (change p 116 (some 138)) := by
  have certified := compare1190 p (guard215 p guard)
  change d312 p ≤ (0 : Int) + d516 (change p 116 (some 138))
  have normalized := agree516 _ _ (change_representative support p 116 (some 138) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (0 : Int) + d516 (change p 116 (some 138))
  rw [sub2246]
  exact certified
theorem check215 (p : Pattern) : (!pushGuard support p 94 116 138 138 || decide (bonus 94 p ≤ 1 + Generated.soko2_2Potential.boulder 138 - Generated.soko2_2Potential.boulder 116 + bonus 116 (change p 116 (some 138)))) = true :=
  check_of_implication _ _ (bound215 p)
end NetHack.Sokoban22Refined85
