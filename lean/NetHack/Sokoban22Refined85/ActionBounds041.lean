import NetHack.Sokoban22Refined85.ActionBounds040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard984 (p : Pattern) (guard : pushGuard support p 248 249 250 250 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound984 (p : Pattern) (guard : pushGuard support p 248 249 250 250 = true) : bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.boulder 249 + bonus 249 (change p 249 (some 250)) := by
  have certified := compare24907 p (guard984 p guard)
  change d3224 p ≤ (0 : Int) + d3224 (change p 249 (some 250))
  have normalized := agree3224 _ _ (change_representative support p 249 (some 250) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check984 (p : Pattern) : (!pushGuard support p 248 249 250 250 || decide (bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.boulder 249 + bonus 249 (change p 249 (some 250)))) = true :=
  check_of_implication _ _ (bound984 p)
theorem guard985 (p : Pattern) (guard : pushGuard support p 248 249 250 250 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound985 (p : Pattern) (guard : pushGuard support p 248 249 250 250 = true) : bonus 248 p ≤ 1 - Generated.soko2_2Potential.boulder 249 - Generated.soko2_2Potential.hole 250 + bonus 249 (change p 249 none) := by
  have certified := compare24907 p (guard985 p guard)
  change d3224 p ≤ (0 : Int) + d3224 (change p 249 none)
  have normalized := agree3224 _ _ (change_representative support p 249 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check985 (p : Pattern) : (!pushGuard support p 248 249 250 250 || decide (bonus 248 p ≤ 1 - Generated.soko2_2Potential.boulder 249 - Generated.soko2_2Potential.hole 250 + bonus 249 (change p 249 none))) = true :=
  check_of_implication _ _ (bound985 p)
theorem guard986 (p : Pattern) (guard : walkGuard soko2_2.board support p 248 247 .west = true) : d5843 p = 1 := by
  change (!false && !(p 247) && !false) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound986 (p : Pattern) (guard : walkGuard soko2_2.board support p 248 247 .west = true) : bonus 248 p ≤ bonus 247 p := by
  have certified := compare26330 p (guard986 p guard)
  simpa only [at248, at247, Int.zero_add] using certified
theorem check986 (p : Pattern) : (!walkGuard soko2_2.board support p 248 247 .west || decide (bonus 248 p ≤ bonus 247 p)) = true :=
  check_of_implication _ _ (bound986 p)
theorem guard987 (p : Pattern) (guard : pushGuard support p 248 247 246 246 = true) : d6558 p = 1 := by
  change (!false && (!true || (p 247)) && !(p 246) && (!(p 246) || false)) = true at guard
  cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5842, d6558, h246, h247] at guard ⊢
theorem bound987 (p : Pattern) (guard : pushGuard support p 248 247 246 246 = true) : bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder 246 - Generated.soko2_2Potential.boulder 247 + bonus 247 (change p 247 (some 246)) := by
  have certified := compare33242 p (guard987 p guard)
  change d3224 p ≤ (2 : Int) + d4036 (change p 247 (some 246))
  have normalized := agree4036 _ _ (change_representative support p 247 (some 246) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (2 : Int) + d4036 (change p 247 (some 246))
  rw [sub13652]
  exact certified
theorem check987 (p : Pattern) : (!pushGuard support p 248 247 246 246 || decide (bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder 246 - Generated.soko2_2Potential.boulder 247 + bonus 247 (change p 247 (some 246)))) = true :=
  check_of_implication _ _ (bound987 p)
theorem guard988 (p : Pattern) (guard : walkGuard soko2_2.board support p 248 225 .northWest = true) : d5502 p = 1 := by
  change (!false && !(p 225) && !(true && false && (p 247))) = true at guard
  cases h225 : p 225 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5502, h225, h247] at guard ⊢
theorem bound988 (p : Pattern) (guard : walkGuard soko2_2.board support p 248 225 .northWest = true) : bonus 248 p ≤ bonus 225 p := by
  have certified := compare25321 p (guard988 p guard)
  simpa only [at248, at225, Int.zero_add] using certified
theorem check988 (p : Pattern) : (!walkGuard soko2_2.board support p 248 225 .northWest || decide (bonus 248 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound988 p)
theorem guard989 (p : Pattern) (guard : walkGuard soko2_2.board support p 249 250 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound989 (p : Pattern) (guard : walkGuard soko2_2.board support p 249 250 .east = true) : bonus 249 p ≤ bonus 250 p := by
  have certified := compare24907 p (guard989 p guard)
  simpa only [at249, at250, Int.zero_add] using certified
theorem check989 (p : Pattern) : (!walkGuard soko2_2.board support p 249 250 .east || decide (bonus 249 p ≤ bonus 250 p)) = true :=
  check_of_implication _ _ (bound989 p)
theorem guard990 (p : Pattern) (guard : pushGuard support p 249 250 251 251 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound990 (p : Pattern) (guard : pushGuard support p 249 250 251 251 = true) : bonus 249 p ≤ 1 + Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.boulder 250 + bonus 250 (change p 250 (some 251)) := by
  have certified := compare33243 p (guard990 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 250 (some 251))
  have normalized := agree3224 _ _ (change_representative support p 250 (some 251) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check990 (p : Pattern) : (!pushGuard support p 249 250 251 251 || decide (bonus 249 p ≤ 1 + Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.boulder 250 + bonus 250 (change p 250 (some 251)))) = true :=
  check_of_implication _ _ (bound990 p)
theorem guard991 (p : Pattern) (guard : pushGuard support p 249 250 251 251 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound991 (p : Pattern) (guard : pushGuard support p 249 250 251 251 = true) : bonus 249 p ≤ 1 - Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.hole 251 + bonus 250 (change p 250 none) := by
  have certified := compare33243 p (guard991 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 250 none)
  have normalized := agree3224 _ _ (change_representative support p 250 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check991 (p : Pattern) : (!pushGuard support p 249 250 251 251 || decide (bonus 249 p ≤ 1 - Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.hole 251 + bonus 250 (change p 250 none))) = true :=
  check_of_implication _ _ (bound991 p)
theorem guard992 (p : Pattern) (guard : walkGuard soko2_2.board support p 249 248 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound992 (p : Pattern) (guard : walkGuard soko2_2.board support p 249 248 .west = true) : bonus 249 p ≤ bonus 248 p := by
  have certified := compare24907 p (guard992 p guard)
  simpa only [at249, at248, Int.zero_add] using certified
theorem check992 (p : Pattern) : (!walkGuard soko2_2.board support p 249 248 .west || decide (bonus 249 p ≤ bonus 248 p)) = true :=
  check_of_implication _ _ (bound992 p)
theorem guard993 (p : Pattern) (guard : pushGuard support p 249 248 247 247 = true) : d5843 p = 1 := by
  change (!false && (!false || false) && !(p 247) && (!(p 247) || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound993 (p : Pattern) (guard : pushGuard support p 249 248 247 247 = true) : bonus 249 p ≤ 1 + Generated.soko2_2Potential.boulder 247 - Generated.soko2_2Potential.boulder 248 + bonus 248 (change p 248 (some 247)) := by
  have certified := compare33792 p (guard993 p guard)
  change d3224 p ≤ (2 : Int) + d3224 (change p 248 (some 247))
  have normalized := agree3224 _ _ (change_representative support p 248 (some 247) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (2 : Int) + d3224 (change p 10000 (some 247))
  rw [sub14191]
  exact certified
theorem check993 (p : Pattern) : (!pushGuard support p 249 248 247 247 || decide (bonus 249 p ≤ 1 + Generated.soko2_2Potential.boulder 247 - Generated.soko2_2Potential.boulder 248 + bonus 248 (change p 248 (some 247)))) = true :=
  check_of_implication _ _ (bound993 p)
theorem guard994 (p : Pattern) (guard : walkGuard soko2_2.board support p 249 226 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound994 (p : Pattern) (guard : walkGuard soko2_2.board support p 249 226 .northWest = true) : bonus 249 p ≤ bonus 226 p := by
  have certified := compare24907 p (guard994 p guard)
  simpa only [at249, at226, Int.zero_add] using certified
theorem check994 (p : Pattern) : (!walkGuard soko2_2.board support p 249 226 .northWest || decide (bonus 249 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound994 p)
theorem guard995 (p : Pattern) (guard : walkGuard soko2_2.board support p 250 251 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound995 (p : Pattern) (guard : walkGuard soko2_2.board support p 250 251 .east = true) : bonus 250 p ≤ bonus 251 p := by
  have certified := compare24907 p (guard995 p guard)
  simpa only [at250, at251, Int.zero_add] using certified
theorem check995 (p : Pattern) : (!walkGuard soko2_2.board support p 250 251 .east || decide (bonus 250 p ≤ bonus 251 p)) = true :=
  check_of_implication _ _ (bound995 p)
theorem guard996 (p : Pattern) (guard : pushGuard support p 250 251 252 252 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound996 (p : Pattern) (guard : pushGuard support p 250 251 252 252 = true) : bonus 250 p ≤ 1 + Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.boulder 251 + bonus 251 (change p 251 (some 252)) := by
  have certified := compare33243 p (guard996 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 251 (some 252))
  have normalized := agree3224 _ _ (change_representative support p 251 (some 252) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check996 (p : Pattern) : (!pushGuard support p 250 251 252 252 || decide (bonus 250 p ≤ 1 + Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.boulder 251 + bonus 251 (change p 251 (some 252)))) = true :=
  check_of_implication _ _ (bound996 p)
theorem guard997 (p : Pattern) (guard : pushGuard support p 250 251 252 252 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound997 (p : Pattern) (guard : pushGuard support p 250 251 252 252 = true) : bonus 250 p ≤ 1 - Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.hole 252 + bonus 251 (change p 251 none) := by
  have certified := compare33243 p (guard997 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 251 none)
  have normalized := agree3224 _ _ (change_representative support p 251 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check997 (p : Pattern) : (!pushGuard support p 250 251 252 252 || decide (bonus 250 p ≤ 1 - Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.hole 252 + bonus 251 (change p 251 none))) = true :=
  check_of_implication _ _ (bound997 p)
theorem guard998 (p : Pattern) (guard : walkGuard soko2_2.board support p 250 249 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound998 (p : Pattern) (guard : walkGuard soko2_2.board support p 250 249 .west = true) : bonus 250 p ≤ bonus 249 p := by
  have certified := compare24907 p (guard998 p guard)
  simpa only [at250, at249, Int.zero_add] using certified
theorem check998 (p : Pattern) : (!walkGuard soko2_2.board support p 250 249 .west || decide (bonus 250 p ≤ bonus 249 p)) = true :=
  check_of_implication _ _ (bound998 p)
theorem guard999 (p : Pattern) (guard : pushGuard support p 250 249 248 248 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound999 (p : Pattern) (guard : pushGuard support p 250 249 248 248 = true) : bonus 250 p ≤ 1 + Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.boulder 249 + bonus 249 (change p 249 (some 248)) := by
  have certified := compare33243 p (guard999 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 249 (some 248))
  have normalized := agree3224 _ _ (change_representative support p 249 (some 248) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check999 (p : Pattern) : (!pushGuard support p 250 249 248 248 || decide (bonus 250 p ≤ 1 + Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.boulder 249 + bonus 249 (change p 249 (some 248)))) = true :=
  check_of_implication _ _ (bound999 p)
theorem guard1000 (p : Pattern) (guard : walkGuard soko2_2.board support p 251 252 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1000 (p : Pattern) (guard : walkGuard soko2_2.board support p 251 252 .east = true) : bonus 251 p ≤ bonus 252 p := by
  have certified := compare24907 p (guard1000 p guard)
  simpa only [at251, at252, Int.zero_add] using certified
theorem check1000 (p : Pattern) : (!walkGuard soko2_2.board support p 251 252 .east || decide (bonus 251 p ≤ bonus 252 p)) = true :=
  check_of_implication _ _ (bound1000 p)
theorem guard1001 (p : Pattern) (guard : pushGuard support p 251 252 253 253 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1001 (p : Pattern) (guard : pushGuard support p 251 252 253 253 = true) : bonus 251 p ≤ 1 + Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.boulder 252 + bonus 252 (change p 252 (some 253)) := by
  have certified := compare33243 p (guard1001 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 252 (some 253))
  have normalized := agree3224 _ _ (change_representative support p 252 (some 253) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1001 (p : Pattern) : (!pushGuard support p 251 252 253 253 || decide (bonus 251 p ≤ 1 + Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.boulder 252 + bonus 252 (change p 252 (some 253)))) = true :=
  check_of_implication _ _ (bound1001 p)
theorem guard1002 (p : Pattern) (guard : pushGuard support p 251 252 253 253 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1002 (p : Pattern) (guard : pushGuard support p 251 252 253 253 = true) : bonus 251 p ≤ 1 - Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.hole 253 + bonus 252 (change p 252 none) := by
  have certified := compare33243 p (guard1002 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 252 none)
  have normalized := agree3224 _ _ (change_representative support p 252 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1002 (p : Pattern) : (!pushGuard support p 251 252 253 253 || decide (bonus 251 p ≤ 1 - Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.hole 253 + bonus 252 (change p 252 none))) = true :=
  check_of_implication _ _ (bound1002 p)
theorem guard1003 (p : Pattern) (guard : walkGuard soko2_2.board support p 251 250 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1003 (p : Pattern) (guard : walkGuard soko2_2.board support p 251 250 .west = true) : bonus 251 p ≤ bonus 250 p := by
  have certified := compare24907 p (guard1003 p guard)
  simpa only [at251, at250, Int.zero_add] using certified
theorem check1003 (p : Pattern) : (!walkGuard soko2_2.board support p 251 250 .west || decide (bonus 251 p ≤ bonus 250 p)) = true :=
  check_of_implication _ _ (bound1003 p)
theorem guard1004 (p : Pattern) (guard : pushGuard support p 251 250 249 245 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1004 (p : Pattern) (guard : pushGuard support p 251 250 249 245 = true) : bonus 251 p ≤ 1 + Generated.soko2_2Potential.boulder 245 - Generated.soko2_2Potential.boulder 250 + bonus 250 (change p 250 (some 245)) := by
  have certified := compare33793 p (guard1004 p guard)
  change d3224 p ≤ (12 : Int) + d3224 (change p 250 (some 245))
  have normalized := agree3224 _ _ (change_representative support p 250 (some 245) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (12 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1004 (p : Pattern) : (!pushGuard support p 251 250 249 245 || decide (bonus 251 p ≤ 1 + Generated.soko2_2Potential.boulder 245 - Generated.soko2_2Potential.boulder 250 + bonus 250 (change p 250 (some 245)))) = true :=
  check_of_implication _ _ (bound1004 p)
theorem guard1005 (p : Pattern) (guard : pushGuard support p 251 250 249 250 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1005 (p : Pattern) (guard : pushGuard support p 251 250 249 250 = true) : bonus 251 p ≤ 1 - Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.hole 250 + bonus 250 (change p 250 none) := by
  have certified := compare33243 p (guard1005 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 250 none)
  have normalized := agree3224 _ _ (change_representative support p 250 none 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1005 (p : Pattern) : (!pushGuard support p 251 250 249 250 || decide (bonus 251 p ≤ 1 - Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.hole 250 + bonus 250 (change p 250 none))) = true :=
  check_of_implication _ _ (bound1005 p)
theorem guard1006 (p : Pattern) (guard : walkGuard soko2_2.board support p 252 253 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1006 (p : Pattern) (guard : walkGuard soko2_2.board support p 252 253 .east = true) : bonus 252 p ≤ bonus 253 p := by
  have certified := compare24907 p (guard1006 p guard)
  simpa only [at252, at253, Int.zero_add] using certified
theorem check1006 (p : Pattern) : (!walkGuard soko2_2.board support p 252 253 .east || decide (bonus 252 p ≤ bonus 253 p)) = true :=
  check_of_implication _ _ (bound1006 p)
theorem guard1007 (p : Pattern) (guard : pushGuard support p 252 253 254 254 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1007 (p : Pattern) (guard : pushGuard support p 252 253 254 254 = true) : bonus 252 p ≤ 1 + Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.boulder 253 + bonus 253 (change p 253 (some 254)) := by
  have certified := compare33243 p (guard1007 p guard)
  change d3224 p ≤ (1 : Int) + d3224 (change p 253 (some 254))
  have normalized := agree3224 _ _ (change_representative support p 253 (some 254) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (1 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check1007 (p : Pattern) : (!pushGuard support p 252 253 254 254 || decide (bonus 252 p ≤ 1 + Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.boulder 253 + bonus 253 (change p 253 (some 254)))) = true :=
  check_of_implication _ _ (bound1007 p)
end NetHack.Sokoban22Refined85
