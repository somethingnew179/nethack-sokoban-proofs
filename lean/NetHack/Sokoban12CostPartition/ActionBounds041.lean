import NetHack.Sokoban12CostPartition.ActionBounds040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard984 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 318 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound984 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 318 .northWest = true) : bonus 345 p ≤ bonus 318 p := by
  have certified := compare897 p (guard984 p guard)
  simpa only [at345, at318, Int.zero_add] using certified
theorem check984 (p : Pattern) : (!walkGuard soko1_2.board support p 345 318 .northWest || decide (bonus 345 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound984 p)
theorem guard985 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 372 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound985 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 372 .southEast = true) : bonus 345 p ≤ bonus 372 p := by
  have certified := compare897 p (guard985 p guard)
  simpa only [at345, at372, Int.zero_add] using certified
theorem check985 (p : Pattern) : (!walkGuard soko1_2.board support p 345 372 .southEast || decide (bonus 345 p ≤ bonus 372 p)) = true :=
  check_of_implication _ _ (bound985 p)
theorem guard986 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 370 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound986 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 370 .southWest = true) : bonus 345 p ≤ bonus 370 p := by
  have certified := compare897 p (guard986 p guard)
  simpa only [at345, at370, Int.zero_add] using certified
theorem check986 (p : Pattern) : (!walkGuard soko1_2.board support p 345 370 .southWest || decide (bonus 345 p ≤ bonus 370 p)) = true :=
  check_of_implication _ _ (bound986 p)
theorem guard987 (p : Pattern) (guard : walkGuard soko1_2.board support p 348 322 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound987 (p : Pattern) (guard : walkGuard soko1_2.board support p 348 322 .north = true) : bonus 348 p ≤ bonus 322 p := by
  have certified := compare897 p (guard987 p guard)
  simpa only [at348, at322, Int.zero_add] using certified
theorem check987 (p : Pattern) : (!walkGuard soko1_2.board support p 348 322 .north || decide (bonus 348 p ≤ bonus 322 p)) = true :=
  check_of_implication _ _ (bound987 p)
theorem guard988 (p : Pattern) (guard : pushGuard support p 348 322 296 296 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound988 (p : Pattern) (guard : pushGuard support p 348 322 296 296 = true) : bonus 348 p ≤ 1 + Generated.soko1_2Potential.boulder 296 - Generated.soko1_2Potential.boulder 322 + bonus 322 (change p 322 (some 296)) := by
  have certified := compare5431 p (guard988 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 322 (some 296))
  have normalized := agree258 _ _ (change_representative support p 322 (some 296) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check988 (p : Pattern) : (!pushGuard support p 348 322 296 296 || decide (bonus 348 p ≤ 1 + Generated.soko1_2Potential.boulder 296 - Generated.soko1_2Potential.boulder 322 + bonus 322 (change p 322 (some 296)))) = true :=
  check_of_implication _ _ (bound988 p)
theorem guard989 (p : Pattern) (guard : walkGuard soko1_2.board support p 348 374 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound989 (p : Pattern) (guard : walkGuard soko1_2.board support p 348 374 .south = true) : bonus 348 p ≤ bonus 374 p := by
  have certified := compare897 p (guard989 p guard)
  simpa only [at348, at374, Int.zero_add] using certified
theorem check989 (p : Pattern) : (!walkGuard soko1_2.board support p 348 374 .south || decide (bonus 348 p ≤ bonus 374 p)) = true :=
  check_of_implication _ _ (bound989 p)
theorem guard990 (p : Pattern) (guard : pushGuard support p 348 374 400 400 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound990 (p : Pattern) (guard : pushGuard support p 348 374 400 400 = true) : bonus 348 p ≤ 1 + Generated.soko1_2Potential.boulder 400 - Generated.soko1_2Potential.boulder 374 + bonus 374 (change p 374 (some 400)) := by
  have certified := compare5431 p (guard990 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 374 (some 400))
  have normalized := agree258 _ _ (change_representative support p 374 (some 400) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check990 (p : Pattern) : (!pushGuard support p 348 374 400 400 || decide (bonus 348 p ≤ 1 + Generated.soko1_2Potential.boulder 400 - Generated.soko1_2Potential.boulder 374 + bonus 374 (change p 374 (some 400)))) = true :=
  check_of_implication _ _ (bound990 p)
theorem guard991 (p : Pattern) (guard : walkGuard soko1_2.board support p 348 373 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound991 (p : Pattern) (guard : walkGuard soko1_2.board support p 348 373 .southWest = true) : bonus 348 p ≤ bonus 373 p := by
  have certified := compare897 p (guard991 p guard)
  simpa only [at348, at373, Int.zero_add] using certified
theorem check991 (p : Pattern) : (!walkGuard soko1_2.board support p 348 373 .southWest || decide (bonus 348 p ≤ bonus 373 p)) = true :=
  check_of_implication _ _ (bound991 p)
theorem guard992 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 330 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound992 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 330 .north = true) : bonus 356 p ≤ bonus 330 p := by
  have certified := compare898 p (guard992 p guard)
  simpa only [at356, at330, Int.zero_add] using certified
theorem check992 (p : Pattern) : (!walkGuard soko1_2.board support p 356 330 .north || decide (bonus 356 p ≤ bonus 330 p)) = true :=
  check_of_implication _ _ (bound992 p)
theorem guard993 (p : Pattern) (guard : pushGuard support p 356 330 304 304 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound993 (p : Pattern) (guard : pushGuard support p 356 330 304 304 = true) : bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder 304 - Generated.soko1_2Potential.boulder 330 + bonus 330 (change p 330 (some 304)) := by
  have certified := compare1005 p (guard993 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 330 (some 304))
  have normalized := agree0 _ _ (change_representative support p 330 (some 304) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check993 (p : Pattern) : (!pushGuard support p 356 330 304 304 || decide (bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder 304 - Generated.soko1_2Potential.boulder 330 + bonus 330 (change p 330 (some 304)))) = true :=
  check_of_implication _ _ (bound993 p)
theorem guard994 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 382 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound994 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 382 .south = true) : bonus 356 p ≤ bonus 382 p := by
  have certified := compare898 p (guard994 p guard)
  simpa only [at356, at382, Int.zero_add] using certified
theorem check994 (p : Pattern) : (!walkGuard soko1_2.board support p 356 382 .south || decide (bonus 356 p ≤ bonus 382 p)) = true :=
  check_of_implication _ _ (bound994 p)
theorem guard995 (p : Pattern) (guard : pushGuard support p 356 382 408 408 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound995 (p : Pattern) (guard : pushGuard support p 356 382 408 408 = true) : bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder 408 - Generated.soko1_2Potential.boulder 382 + bonus 382 (change p 382 (some 408)) := by
  have certified := compare1005 p (guard995 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 382 (some 408))
  have normalized := agree0 _ _ (change_representative support p 382 (some 408) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check995 (p : Pattern) : (!pushGuard support p 356 382 408 408 || decide (bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder 408 - Generated.soko1_2Potential.boulder 382 + bonus 382 (change p 382 (some 408)))) = true :=
  check_of_implication _ _ (bound995 p)
theorem guard996 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 357 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound996 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 357 .east = true) : bonus 356 p ≤ bonus 357 p := by
  have certified := compare898 p (guard996 p guard)
  simpa only [at356, at357, Int.zero_add] using certified
theorem check996 (p : Pattern) : (!walkGuard soko1_2.board support p 356 357 .east || decide (bonus 356 p ≤ bonus 357 p)) = true :=
  check_of_implication _ _ (bound996 p)
theorem guard997 (p : Pattern) (guard : pushGuard support p 356 357 358 358 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound997 (p : Pattern) (guard : pushGuard support p 356 357 358 358 = true) : bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some 358)) := by
  have certified := compare1005 p (guard997 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 357 (some 358))
  have normalized := agree0 _ _ (change_representative support p 357 (some 358) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check997 (p : Pattern) : (!pushGuard support p 356 357 358 358 || decide (bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some 358)))) = true :=
  check_of_implication _ _ (bound997 p)
theorem guard998 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 331 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound998 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 331 .northEast = true) : bonus 356 p ≤ bonus 331 p := by
  have certified := compare898 p (guard998 p guard)
  simpa only [at356, at331, Int.zero_add] using certified
theorem check998 (p : Pattern) : (!walkGuard soko1_2.board support p 356 331 .northEast || decide (bonus 356 p ≤ bonus 331 p)) = true :=
  check_of_implication _ _ (bound998 p)
theorem guard999 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 383 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound999 (p : Pattern) (guard : walkGuard soko1_2.board support p 356 383 .southEast = true) : bonus 356 p ≤ bonus 383 p := by
  have certified := compare898 p (guard999 p guard)
  simpa only [at356, at383, Int.zero_add] using certified
theorem check999 (p : Pattern) : (!walkGuard soko1_2.board support p 356 383 .southEast || decide (bonus 356 p ≤ bonus 383 p)) = true :=
  check_of_implication _ _ (bound999 p)
theorem guard1000 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 331 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1000 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 331 .north = true) : bonus 357 p ≤ bonus 331 p := by
  have certified := compare898 p (guard1000 p guard)
  simpa only [at357, at331, Int.zero_add] using certified
theorem check1000 (p : Pattern) : (!walkGuard soko1_2.board support p 357 331 .north || decide (bonus 357 p ≤ bonus 331 p)) = true :=
  check_of_implication _ _ (bound1000 p)
theorem guard1001 (p : Pattern) (guard : pushGuard support p 357 331 305 305 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1001 (p : Pattern) (guard : pushGuard support p 357 331 305 305 = true) : bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some 305)) := by
  have certified := compare1005 p (guard1001 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 331 (some 305))
  have normalized := agree0 _ _ (change_representative support p 331 (some 305) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1001 (p : Pattern) : (!pushGuard support p 357 331 305 305 || decide (bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some 305)))) = true :=
  check_of_implication _ _ (bound1001 p)
theorem guard1002 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 383 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1002 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 383 .south = true) : bonus 357 p ≤ bonus 383 p := by
  have certified := compare898 p (guard1002 p guard)
  simpa only [at357, at383, Int.zero_add] using certified
theorem check1002 (p : Pattern) : (!walkGuard soko1_2.board support p 357 383 .south || decide (bonus 357 p ≤ bonus 383 p)) = true :=
  check_of_implication _ _ (bound1002 p)
theorem guard1003 (p : Pattern) (guard : pushGuard support p 357 383 409 409 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1003 (p : Pattern) (guard : pushGuard support p 357 383 409 409 = true) : bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder 409 - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some 409)) := by
  have certified := compare1005 p (guard1003 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 383 (some 409))
  have normalized := agree0 _ _ (change_representative support p 383 (some 409) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1003 (p : Pattern) : (!pushGuard support p 357 383 409 409 || decide (bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder 409 - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some 409)))) = true :=
  check_of_implication _ _ (bound1003 p)
theorem guard1004 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 358 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1004 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 358 .east = true) : bonus 357 p ≤ bonus 358 p := by
  have certified := compare898 p (guard1004 p guard)
  simpa only [at357, at358, Int.zero_add] using certified
theorem check1004 (p : Pattern) : (!walkGuard soko1_2.board support p 357 358 .east || decide (bonus 357 p ≤ bonus 358 p)) = true :=
  check_of_implication _ _ (bound1004 p)
theorem guard1005 (p : Pattern) (guard : pushGuard support p 357 358 359 359 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1005 (p : Pattern) (guard : pushGuard support p 357 358 359 359 = true) : bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some 359)) := by
  have certified := compare1005 p (guard1005 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 358 (some 359))
  have normalized := agree0 _ _ (change_representative support p 358 (some 359) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check1005 (p : Pattern) : (!pushGuard support p 357 358 359 359 || decide (bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some 359)))) = true :=
  check_of_implication _ _ (bound1005 p)
theorem guard1006 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 356 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1006 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 356 .west = true) : bonus 357 p ≤ bonus 356 p := by
  have certified := compare898 p (guard1006 p guard)
  simpa only [at357, at356, Int.zero_add] using certified
theorem check1006 (p : Pattern) : (!walkGuard soko1_2.board support p 357 356 .west || decide (bonus 357 p ≤ bonus 356 p)) = true :=
  check_of_implication _ _ (bound1006 p)
theorem guard1007 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 332 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1007 (p : Pattern) (guard : walkGuard soko1_2.board support p 357 332 .northEast = true) : bonus 357 p ≤ bonus 332 p := by
  have certified := compare898 p (guard1007 p guard)
  simpa only [at357, at332, Int.zero_add] using certified
theorem check1007 (p : Pattern) : (!walkGuard soko1_2.board support p 357 332 .northEast || decide (bonus 357 p ≤ bonus 332 p)) = true :=
  check_of_implication _ _ (bound1007 p)
end NetHack.Sokoban12CostPartition
