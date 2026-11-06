import NetHack.Sokoban32Refined.ActionBounds040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard984 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 216 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound984 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 216 .east = true) : bonus 215 p ≤ bonus 216 p := by
  have certified := compare0 p (guard984 p guard)
  simpa only [at215, at216, Int.zero_add] using certified
theorem check984 (p : Pattern) : (!walkGuard soko3_2.board support p 215 216 .east || decide (bonus 215 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound984 p)
theorem guard985 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 214 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound985 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 214 .west = true) : bonus 215 p ≤ bonus 214 p := by
  have certified := compare0 p (guard985 p guard)
  simpa only [at215, at214, Int.zero_add] using certified
theorem check985 (p : Pattern) : (!walkGuard soko3_2.board support p 215 214 .west || decide (bonus 215 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound985 p)
theorem guard986 (p : Pattern) (guard : pushGuard support p 215 214 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound986 (p : Pattern) (guard : pushGuard support p 215 214 213 213 = true) : bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder 213 - Generated.soko3_2Potential.boulder 214 + bonus 214 (change p 214 (some 213)) := by
  have certified := compare4301 p (guard986 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 214 (some 213))
  have normalized := agree134 _ _ (change_representative support p 214 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check986 (p : Pattern) : (!pushGuard support p 215 214 213 213 || decide (bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder 213 - Generated.soko3_2Potential.boulder 214 + bonus 214 (change p 214 (some 213)))) = true :=
  check_of_implication _ _ (bound986 p)
theorem guard987 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 188 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound987 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 188 .northWest = true) : bonus 215 p ≤ bonus 188 p := by
  have certified := compare0 p (guard987 p guard)
  simpa only [at215, at188, Int.zero_add] using certified
theorem check987 (p : Pattern) : (!walkGuard soko3_2.board support p 215 188 .northWest || decide (bonus 215 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound987 p)
theorem guard988 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 242 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound988 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 242 .southEast = true) : bonus 215 p ≤ bonus 242 p := by
  have certified := compare0 p (guard988 p guard)
  simpa only [at215, at242, Int.zero_add] using certified
theorem check988 (p : Pattern) : (!walkGuard soko3_2.board support p 215 242 .southEast || decide (bonus 215 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound988 p)
theorem guard989 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 242 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound989 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 242 .south = true) : bonus 216 p ≤ bonus 242 p := by
  have certified := compare0 p (guard989 p guard)
  simpa only [at216, at242, Int.zero_add] using certified
theorem check989 (p : Pattern) : (!walkGuard soko3_2.board support p 216 242 .south || decide (bonus 216 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound989 p)
theorem guard990 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 215 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound990 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 215 .west = true) : bonus 216 p ≤ bonus 215 p := by
  have certified := compare0 p (guard990 p guard)
  simpa only [at216, at215, Int.zero_add] using certified
theorem check990 (p : Pattern) : (!walkGuard soko3_2.board support p 216 215 .west || decide (bonus 216 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound990 p)
theorem guard991 (p : Pattern) (guard : pushGuard support p 216 215 214 214 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound991 (p : Pattern) (guard : pushGuard support p 216 215 214 214 = true) : bonus 216 p ≤ 1 + Generated.soko3_2Potential.boulder 214 - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some 214)) := by
  have certified := compare4301 p (guard991 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 215 (some 214))
  have normalized := agree134 _ _ (change_representative support p 215 (some 214) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check991 (p : Pattern) : (!pushGuard support p 216 215 214 214 || decide (bonus 216 p ≤ 1 + Generated.soko3_2Potential.boulder 214 - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some 214)))) = true :=
  check_of_implication _ _ (bound991 p)
theorem guard992 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 189 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound992 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 189 .northWest = true) : bonus 216 p ≤ bonus 189 p := by
  have certified := compare0 p (guard992 p guard)
  simpa only [at216, at189, Int.zero_add] using certified
theorem check992 (p : Pattern) : (!walkGuard soko3_2.board support p 216 189 .northWest || decide (bonus 216 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound992 p)
theorem guard993 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 243 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound993 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 243 .southEast = true) : bonus 216 p ≤ bonus 243 p := by
  have certified := compare0 p (guard993 p guard)
  simpa only [at216, at243, Int.zero_add] using certified
theorem check993 (p : Pattern) : (!walkGuard soko3_2.board support p 216 243 .southEast || decide (bonus 216 p ≤ bonus 243 p)) = true :=
  check_of_implication _ _ (bound993 p)
theorem guard994 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 241 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound994 (p : Pattern) (guard : walkGuard soko3_2.board support p 216 241 .southWest = true) : bonus 216 p ≤ bonus 241 p := by
  have certified := compare0 p (guard994 p guard)
  simpa only [at216, at241, Int.zero_add] using certified
theorem check994 (p : Pattern) : (!walkGuard soko3_2.board support p 216 241 .southWest || decide (bonus 216 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound994 p)
theorem guard995 (p : Pattern) (guard : walkGuard soko3_2.board support p 218 192 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound995 (p : Pattern) (guard : walkGuard soko3_2.board support p 218 192 .north = true) : bonus 218 p ≤ bonus 192 p := by
  have certified := compare0 p (guard995 p guard)
  simpa only [at218, at192, Int.zero_add] using certified
theorem check995 (p : Pattern) : (!walkGuard soko3_2.board support p 218 192 .north || decide (bonus 218 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound995 p)
theorem guard996 (p : Pattern) (guard : pushGuard support p 218 192 166 166 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound996 (p : Pattern) (guard : pushGuard support p 218 192 166 166 = true) : bonus 218 p ≤ 1 + Generated.soko3_2Potential.boulder 166 - Generated.soko3_2Potential.boulder 192 + bonus 192 (change p 192 (some 166)) := by
  have certified := compare9362 p (guard996 p guard)
  change d134 p ≤ (15 : Int) + d134 (change p 192 (some 166))
  have normalized := agree134 _ _ (change_representative support p 192 (some 166) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (15 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check996 (p : Pattern) : (!pushGuard support p 218 192 166 166 || decide (bonus 218 p ≤ 1 + Generated.soko3_2Potential.boulder 166 - Generated.soko3_2Potential.boulder 192 + bonus 192 (change p 192 (some 166)))) = true :=
  check_of_implication _ _ (bound996 p)
theorem guard997 (p : Pattern) (guard : walkGuard soko3_2.board support p 218 244 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound997 (p : Pattern) (guard : walkGuard soko3_2.board support p 218 244 .south = true) : bonus 218 p ≤ bonus 244 p := by
  have certified := compare0 p (guard997 p guard)
  simpa only [at218, at244, Int.zero_add] using certified
theorem check997 (p : Pattern) : (!walkGuard soko3_2.board support p 218 244 .south || decide (bonus 218 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound997 p)
theorem guard998 (p : Pattern) (guard : pushGuard support p 218 244 270 270 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound998 (p : Pattern) (guard : pushGuard support p 218 244 270 270 = true) : bonus 218 p ≤ 1 + Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some 270)) := by
  have certified := compare0 p (guard998 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 244 (some 270))
  have normalized := agree134 _ _ (change_representative support p 244 (some 270) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check998 (p : Pattern) : (!pushGuard support p 218 244 270 270 || decide (bonus 218 p ≤ 1 + Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some 270)))) = true :=
  check_of_implication _ _ (bound998 p)
theorem guard999 (p : Pattern) (guard : walkGuard soko3_2.board support p 218 245 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound999 (p : Pattern) (guard : walkGuard soko3_2.board support p 218 245 .southEast = true) : bonus 218 p ≤ bonus 245 p := by
  have certified := compare0 p (guard999 p guard)
  simpa only [at218, at245, Int.zero_add] using certified
theorem check999 (p : Pattern) : (!walkGuard soko3_2.board support p 218 245 .southEast || decide (bonus 218 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound999 p)
theorem guard1000 (p : Pattern) (guard : walkGuard soko3_2.board support p 218 243 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1000 (p : Pattern) (guard : walkGuard soko3_2.board support p 218 243 .southWest = true) : bonus 218 p ≤ bonus 243 p := by
  have certified := compare0 p (guard1000 p guard)
  simpa only [at218, at243, Int.zero_add] using certified
theorem check1000 (p : Pattern) : (!walkGuard soko3_2.board support p 218 243 .southWest || decide (bonus 218 p ≤ bonus 243 p)) = true :=
  check_of_implication _ _ (bound1000 p)
theorem guard1001 (p : Pattern) (guard : walkGuard soko3_2.board support p 224 198 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1001 (p : Pattern) (guard : walkGuard soko3_2.board support p 224 198 .north = true) : bonus 224 p ≤ bonus 198 p := by
  have certified := compare103 p (guard1001 p guard)
  simpa only [at224, at198, Int.zero_add] using certified
theorem check1001 (p : Pattern) : (!walkGuard soko3_2.board support p 224 198 .north || decide (bonus 224 p ≤ bonus 198 p)) = true :=
  check_of_implication _ _ (bound1001 p)
theorem guard1002 (p : Pattern) (guard : pushGuard support p 224 198 172 172 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1002 (p : Pattern) (guard : pushGuard support p 224 198 172 172 = true) : bonus 224 p ≤ 1 + Generated.soko3_2Potential.boulder 172 - Generated.soko3_2Potential.boulder 198 + bonus 198 (change p 198 (some 172)) := by
  have certified := compare37 p (guard1002 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 198 (some 172))
  have normalized := agree0 _ _ (change_representative support p 198 (some 172) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1002 (p : Pattern) : (!pushGuard support p 224 198 172 172 || decide (bonus 224 p ≤ 1 + Generated.soko3_2Potential.boulder 172 - Generated.soko3_2Potential.boulder 198 + bonus 198 (change p 198 (some 172)))) = true :=
  check_of_implication _ _ (bound1002 p)
theorem guard1003 (p : Pattern) (guard : walkGuard soko3_2.board support p 224 225 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1003 (p : Pattern) (guard : walkGuard soko3_2.board support p 224 225 .east = true) : bonus 224 p ≤ bonus 225 p := by
  have certified := compare103 p (guard1003 p guard)
  simpa only [at224, at225, Int.zero_add] using certified
theorem check1003 (p : Pattern) : (!walkGuard soko3_2.board support p 224 225 .east || decide (bonus 224 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound1003 p)
theorem guard1004 (p : Pattern) (guard : pushGuard support p 224 225 226 226 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1004 (p : Pattern) (guard : pushGuard support p 224 225 226 226 = true) : bonus 224 p ≤ 1 + Generated.soko3_2Potential.boulder 226 - Generated.soko3_2Potential.boulder 225 + bonus 225 (change p 225 (some 226)) := by
  have certified := compare37 p (guard1004 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 225 (some 226))
  have normalized := agree0 _ _ (change_representative support p 225 (some 226) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1004 (p : Pattern) : (!pushGuard support p 224 225 226 226 || decide (bonus 224 p ≤ 1 + Generated.soko3_2Potential.boulder 226 - Generated.soko3_2Potential.boulder 225 + bonus 225 (change p 225 (some 226)))) = true :=
  check_of_implication _ _ (bound1004 p)
theorem guard1005 (p : Pattern) (guard : walkGuard soko3_2.board support p 224 199 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1005 (p : Pattern) (guard : walkGuard soko3_2.board support p 224 199 .northEast = true) : bonus 224 p ≤ bonus 199 p := by
  have certified := compare103 p (guard1005 p guard)
  simpa only [at224, at199, Int.zero_add] using certified
theorem check1005 (p : Pattern) : (!walkGuard soko3_2.board support p 224 199 .northEast || decide (bonus 224 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound1005 p)
theorem guard1006 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 199 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1006 (p : Pattern) (guard : walkGuard soko3_2.board support p 225 199 .north = true) : bonus 225 p ≤ bonus 199 p := by
  have certified := compare103 p (guard1006 p guard)
  simpa only [at225, at199, Int.zero_add] using certified
theorem check1006 (p : Pattern) : (!walkGuard soko3_2.board support p 225 199 .north || decide (bonus 225 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound1006 p)
theorem guard1007 (p : Pattern) (guard : pushGuard support p 225 199 173 173 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1007 (p : Pattern) (guard : pushGuard support p 225 199 173 173 = true) : bonus 225 p ≤ 1 + Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some 173)) := by
  have certified := compare37 p (guard1007 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 199 (some 173))
  have normalized := agree0 _ _ (change_representative support p 199 (some 173) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check1007 (p : Pattern) : (!pushGuard support p 225 199 173 173 || decide (bonus 225 p ≤ 1 + Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some 173)))) = true :=
  check_of_implication _ _ (bound1007 p)
end NetHack.Sokoban32Refined
