import NetHack.Sokoban32Refined.ActionBounds003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard96 (p : Pattern) (guard : walkGuard soko3_2.board support p 56 55 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound96 (p : Pattern) (guard : walkGuard soko3_2.board support p 56 55 .west = true) : bonus 56 p ≤ bonus 55 p := by
  have certified := compare0 p (guard96 p guard)
  simpa only [at56, at55, Int.zero_add] using certified
theorem check96 (p : Pattern) : (!walkGuard soko3_2.board support p 56 55 .west || decide (bonus 56 p ≤ bonus 55 p)) = true :=
  check_of_implication _ _ (bound96 p)
theorem guard97 (p : Pattern) (guard : pushGuard support p 56 55 54 54 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound97 (p : Pattern) (guard : pushGuard support p 56 55 54 54 = true) : bonus 56 p ≤ 1 + Generated.soko3_2Potential.boulder 54 - Generated.soko3_2Potential.boulder 55 + bonus 55 (change p 55 (some 54)) := by
  have certified := compare104 p (guard97 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 55 (some 54))
  have normalized := agree134 _ _ (change_representative support p 55 (some 54) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check97 (p : Pattern) : (!pushGuard support p 56 55 54 54 || decide (bonus 56 p ≤ 1 + Generated.soko3_2Potential.boulder 54 - Generated.soko3_2Potential.boulder 55 + bonus 55 (change p 55 (some 54)))) = true :=
  check_of_implication _ _ (bound97 p)
theorem guard98 (p : Pattern) (guard : walkGuard soko3_2.board support p 56 29 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound98 (p : Pattern) (guard : walkGuard soko3_2.board support p 56 29 .northWest = true) : bonus 56 p ≤ bonus 29 p := by
  have certified := compare0 p (guard98 p guard)
  simpa only [at56, at29, Int.zero_add] using certified
theorem check98 (p : Pattern) : (!walkGuard soko3_2.board support p 56 29 .northWest || decide (bonus 56 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound98 p)
theorem guard99 (p : Pattern) (guard : walkGuard soko3_2.board support p 57 58 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound99 (p : Pattern) (guard : walkGuard soko3_2.board support p 57 58 .east = true) : bonus 57 p ≤ bonus 58 p := by
  have certified := compare0 p (guard99 p guard)
  simpa only [at57, at58, Int.zero_add] using certified
theorem check99 (p : Pattern) : (!walkGuard soko3_2.board support p 57 58 .east || decide (bonus 57 p ≤ bonus 58 p)) = true :=
  check_of_implication _ _ (bound99 p)
theorem guard100 (p : Pattern) (guard : pushGuard support p 57 58 59 59 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound100 (p : Pattern) (guard : pushGuard support p 57 58 59 59 = true) : bonus 57 p ≤ 1 + Generated.soko3_2Potential.boulder 59 - Generated.soko3_2Potential.boulder 58 + bonus 58 (change p 58 (some 59)) := by
  have certified := compare104 p (guard100 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 58 (some 59))
  have normalized := agree134 _ _ (change_representative support p 58 (some 59) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check100 (p : Pattern) : (!pushGuard support p 57 58 59 59 || decide (bonus 57 p ≤ 1 + Generated.soko3_2Potential.boulder 59 - Generated.soko3_2Potential.boulder 58 + bonus 58 (change p 58 (some 59)))) = true :=
  check_of_implication _ _ (bound100 p)
theorem guard101 (p : Pattern) (guard : walkGuard soko3_2.board support p 57 56 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound101 (p : Pattern) (guard : walkGuard soko3_2.board support p 57 56 .west = true) : bonus 57 p ≤ bonus 56 p := by
  have certified := compare0 p (guard101 p guard)
  simpa only [at57, at56, Int.zero_add] using certified
theorem check101 (p : Pattern) : (!walkGuard soko3_2.board support p 57 56 .west || decide (bonus 57 p ≤ bonus 56 p)) = true :=
  check_of_implication _ _ (bound101 p)
theorem guard102 (p : Pattern) (guard : pushGuard support p 57 56 55 55 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound102 (p : Pattern) (guard : pushGuard support p 57 56 55 55 = true) : bonus 57 p ≤ 1 + Generated.soko3_2Potential.boulder 55 - Generated.soko3_2Potential.boulder 56 + bonus 56 (change p 56 (some 55)) := by
  have certified := compare104 p (guard102 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 56 (some 55))
  have normalized := agree134 _ _ (change_representative support p 56 (some 55) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check102 (p : Pattern) : (!pushGuard support p 57 56 55 55 || decide (bonus 57 p ≤ 1 + Generated.soko3_2Potential.boulder 55 - Generated.soko3_2Potential.boulder 56 + bonus 56 (change p 56 (some 55)))) = true :=
  check_of_implication _ _ (bound102 p)
theorem guard103 (p : Pattern) (guard : walkGuard soko3_2.board support p 58 59 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound103 (p : Pattern) (guard : walkGuard soko3_2.board support p 58 59 .east = true) : bonus 58 p ≤ bonus 59 p := by
  have certified := compare0 p (guard103 p guard)
  simpa only [at58, at59, Int.zero_add] using certified
theorem check103 (p : Pattern) : (!walkGuard soko3_2.board support p 58 59 .east || decide (bonus 58 p ≤ bonus 59 p)) = true :=
  check_of_implication _ _ (bound103 p)
theorem guard104 (p : Pattern) (guard : pushGuard support p 58 59 60 60 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound104 (p : Pattern) (guard : pushGuard support p 58 59 60 60 = true) : bonus 58 p ≤ 1 + Generated.soko3_2Potential.boulder 60 - Generated.soko3_2Potential.boulder 59 + bonus 59 (change p 59 (some 60)) := by
  have certified := compare104 p (guard104 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 59 (some 60))
  have normalized := agree134 _ _ (change_representative support p 59 (some 60) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check104 (p : Pattern) : (!pushGuard support p 58 59 60 60 || decide (bonus 58 p ≤ 1 + Generated.soko3_2Potential.boulder 60 - Generated.soko3_2Potential.boulder 59 + bonus 59 (change p 59 (some 60)))) = true :=
  check_of_implication _ _ (bound104 p)
theorem guard105 (p : Pattern) (guard : walkGuard soko3_2.board support p 58 57 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound105 (p : Pattern) (guard : walkGuard soko3_2.board support p 58 57 .west = true) : bonus 58 p ≤ bonus 57 p := by
  have certified := compare0 p (guard105 p guard)
  simpa only [at58, at57, Int.zero_add] using certified
theorem check105 (p : Pattern) : (!walkGuard soko3_2.board support p 58 57 .west || decide (bonus 58 p ≤ bonus 57 p)) = true :=
  check_of_implication _ _ (bound105 p)
theorem guard106 (p : Pattern) (guard : pushGuard support p 58 57 56 56 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound106 (p : Pattern) (guard : pushGuard support p 58 57 56 56 = true) : bonus 58 p ≤ 1 + Generated.soko3_2Potential.boulder 56 - Generated.soko3_2Potential.boulder 57 + bonus 57 (change p 57 (some 56)) := by
  have certified := compare104 p (guard106 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 57 (some 56))
  have normalized := agree134 _ _ (change_representative support p 57 (some 56) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check106 (p : Pattern) : (!pushGuard support p 58 57 56 56 || decide (bonus 58 p ≤ 1 + Generated.soko3_2Potential.boulder 56 - Generated.soko3_2Potential.boulder 57 + bonus 57 (change p 57 (some 56)))) = true :=
  check_of_implication _ _ (bound106 p)
theorem guard107 (p : Pattern) (guard : walkGuard soko3_2.board support p 59 60 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound107 (p : Pattern) (guard : walkGuard soko3_2.board support p 59 60 .east = true) : bonus 59 p ≤ bonus 60 p := by
  have certified := compare0 p (guard107 p guard)
  simpa only [at59, at60, Int.zero_add] using certified
theorem check107 (p : Pattern) : (!walkGuard soko3_2.board support p 59 60 .east || decide (bonus 59 p ≤ bonus 60 p)) = true :=
  check_of_implication _ _ (bound107 p)
theorem guard108 (p : Pattern) (guard : pushGuard support p 59 60 61 61 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound108 (p : Pattern) (guard : pushGuard support p 59 60 61 61 = true) : bonus 59 p ≤ 1 + Generated.soko3_2Potential.boulder 61 - Generated.soko3_2Potential.boulder 60 + bonus 60 (change p 60 (some 61)) := by
  have certified := compare104 p (guard108 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 60 (some 61))
  have normalized := agree134 _ _ (change_representative support p 60 (some 61) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check108 (p : Pattern) : (!pushGuard support p 59 60 61 61 || decide (bonus 59 p ≤ 1 + Generated.soko3_2Potential.boulder 61 - Generated.soko3_2Potential.boulder 60 + bonus 60 (change p 60 (some 61)))) = true :=
  check_of_implication _ _ (bound108 p)
theorem guard109 (p : Pattern) (guard : walkGuard soko3_2.board support p 59 58 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound109 (p : Pattern) (guard : walkGuard soko3_2.board support p 59 58 .west = true) : bonus 59 p ≤ bonus 58 p := by
  have certified := compare0 p (guard109 p guard)
  simpa only [at59, at58, Int.zero_add] using certified
theorem check109 (p : Pattern) : (!walkGuard soko3_2.board support p 59 58 .west || decide (bonus 59 p ≤ bonus 58 p)) = true :=
  check_of_implication _ _ (bound109 p)
theorem guard110 (p : Pattern) (guard : pushGuard support p 59 58 57 57 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound110 (p : Pattern) (guard : pushGuard support p 59 58 57 57 = true) : bonus 59 p ≤ 1 + Generated.soko3_2Potential.boulder 57 - Generated.soko3_2Potential.boulder 58 + bonus 58 (change p 58 (some 57)) := by
  have certified := compare104 p (guard110 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 58 (some 57))
  have normalized := agree134 _ _ (change_representative support p 58 (some 57) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check110 (p : Pattern) : (!pushGuard support p 59 58 57 57 || decide (bonus 59 p ≤ 1 + Generated.soko3_2Potential.boulder 57 - Generated.soko3_2Potential.boulder 58 + bonus 58 (change p 58 (some 57)))) = true :=
  check_of_implication _ _ (bound110 p)
theorem guard111 (p : Pattern) (guard : walkGuard soko3_2.board support p 59 86 .southEast = true) : d833 p = 1 := by
  change (!false && !(p 86) && !(true && true && false)) = true at guard
  cases h86 : p 86
  all_goals simp [d0, d1, d833, h86] at guard ⊢
theorem bound111 (p : Pattern) (guard : walkGuard soko3_2.board support p 59 86 .southEast = true) : bonus 59 p ≤ bonus 86 p := by
  have certified := compare197 p (guard111 p guard)
  simpa only [at59, at86, Int.zero_add] using certified
theorem check111 (p : Pattern) : (!walkGuard soko3_2.board support p 59 86 .southEast || decide (bonus 59 p ≤ bonus 86 p)) = true :=
  check_of_implication _ _ (bound111 p)
theorem guard112 (p : Pattern) (guard : walkGuard soko3_2.board support p 60 86 .south = true) : d833 p = 1 := by
  change (!false && !(p 86) && !false) = true at guard
  cases h86 : p 86
  all_goals simp [d0, d1, d833, h86] at guard ⊢
theorem bound112 (p : Pattern) (guard : walkGuard soko3_2.board support p 60 86 .south = true) : bonus 60 p ≤ bonus 86 p := by
  have certified := compare197 p (guard112 p guard)
  simpa only [at60, at86, Int.zero_add] using certified
theorem check112 (p : Pattern) : (!walkGuard soko3_2.board support p 60 86 .south || decide (bonus 60 p ≤ bonus 86 p)) = true :=
  check_of_implication _ _ (bound112 p)
theorem guard113 (p : Pattern) (guard : pushGuard support p 60 86 112 112 = true) : d836 p = 1 := by
  change (!false && (!true || (p 86)) && !(p 112) && (!(p 112) || false)) = true at guard
  cases h86 : p 86 <;> cases h112 : p 112
  all_goals simp [d0, d1, d835, d836, h86, h112] at guard ⊢
theorem bound113 (p : Pattern) (guard : pushGuard support p 60 86 112 112 = true) : bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder 112 - Generated.soko3_2Potential.boulder 86 + bonus 86 (change p 86 (some 112)) := by
  have certified := compare283 p (guard113 p guard)
  change d134 p ≤ (0 : Int) + d176 (change p 86 (some 112))
  have normalized := agree176 _ _ (change_representative support p 86 (some 112) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d176 (change p 86 (some 112))
  rw [sub401]
  exact certified
theorem check113 (p : Pattern) : (!pushGuard support p 60 86 112 112 || decide (bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder 112 - Generated.soko3_2Potential.boulder 86 + bonus 86 (change p 86 (some 112)))) = true :=
  check_of_implication _ _ (bound113 p)
theorem guard114 (p : Pattern) (guard : walkGuard soko3_2.board support p 60 61 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound114 (p : Pattern) (guard : walkGuard soko3_2.board support p 60 61 .east = true) : bonus 60 p ≤ bonus 61 p := by
  have certified := compare0 p (guard114 p guard)
  simpa only [at60, at61, Int.zero_add] using certified
theorem check114 (p : Pattern) : (!walkGuard soko3_2.board support p 60 61 .east || decide (bonus 60 p ≤ bonus 61 p)) = true :=
  check_of_implication _ _ (bound114 p)
theorem guard115 (p : Pattern) (guard : pushGuard support p 60 61 62 62 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound115 (p : Pattern) (guard : pushGuard support p 60 61 62 62 = true) : bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder 62 - Generated.soko3_2Potential.boulder 61 + bonus 61 (change p 61 (some 62)) := by
  have certified := compare104 p (guard115 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 61 (some 62))
  have normalized := agree134 _ _ (change_representative support p 61 (some 62) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check115 (p : Pattern) : (!pushGuard support p 60 61 62 62 || decide (bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder 62 - Generated.soko3_2Potential.boulder 61 + bonus 61 (change p 61 (some 62)))) = true :=
  check_of_implication _ _ (bound115 p)
theorem guard116 (p : Pattern) (guard : walkGuard soko3_2.board support p 60 59 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound116 (p : Pattern) (guard : walkGuard soko3_2.board support p 60 59 .west = true) : bonus 60 p ≤ bonus 59 p := by
  have certified := compare0 p (guard116 p guard)
  simpa only [at60, at59, Int.zero_add] using certified
theorem check116 (p : Pattern) : (!walkGuard soko3_2.board support p 60 59 .west || decide (bonus 60 p ≤ bonus 59 p)) = true :=
  check_of_implication _ _ (bound116 p)
theorem guard117 (p : Pattern) (guard : pushGuard support p 60 59 58 58 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound117 (p : Pattern) (guard : pushGuard support p 60 59 58 58 = true) : bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder 58 - Generated.soko3_2Potential.boulder 59 + bonus 59 (change p 59 (some 58)) := by
  have certified := compare104 p (guard117 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 59 (some 58))
  have normalized := agree134 _ _ (change_representative support p 59 (some 58) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check117 (p : Pattern) : (!pushGuard support p 60 59 58 58 || decide (bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder 58 - Generated.soko3_2Potential.boulder 59 + bonus 59 (change p 59 (some 58)))) = true :=
  check_of_implication _ _ (bound117 p)
theorem guard118 (p : Pattern) (guard : walkGuard soko3_2.board support p 61 62 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound118 (p : Pattern) (guard : walkGuard soko3_2.board support p 61 62 .east = true) : bonus 61 p ≤ bonus 62 p := by
  have certified := compare0 p (guard118 p guard)
  simpa only [at61, at62, Int.zero_add] using certified
theorem check118 (p : Pattern) : (!walkGuard soko3_2.board support p 61 62 .east || decide (bonus 61 p ≤ bonus 62 p)) = true :=
  check_of_implication _ _ (bound118 p)
theorem guard119 (p : Pattern) (guard : walkGuard soko3_2.board support p 61 60 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound119 (p : Pattern) (guard : walkGuard soko3_2.board support p 61 60 .west = true) : bonus 61 p ≤ bonus 60 p := by
  have certified := compare0 p (guard119 p guard)
  simpa only [at61, at60, Int.zero_add] using certified
theorem check119 (p : Pattern) : (!walkGuard soko3_2.board support p 61 60 .west || decide (bonus 61 p ≤ bonus 60 p)) = true :=
  check_of_implication _ _ (bound119 p)
end NetHack.Sokoban32Refined
