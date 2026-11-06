import NetHack.Sokoban22Refined85.ActionBounds003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard96 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 91 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound96 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 91 .south = true) : bonus 69 p ≤ bonus 91 p := by
  have certified := compare0 p (guard96 p guard)
  simpa only [at69, at91, Int.zero_add] using certified
theorem check96 (p : Pattern) : (!walkGuard soko2_2.board support p 69 91 .south || decide (bonus 69 p ≤ bonus 91 p)) = true :=
  check_of_implication _ _ (bound96 p)
theorem guard97 (p : Pattern) (guard : pushGuard support p 69 91 113 113 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound97 (p : Pattern) (guard : pushGuard support p 69 91 113 113 = true) : bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder 113 - Generated.soko2_2Potential.boulder 91 + bonus 91 (change p 91 (some 113)) := by
  have certified := compare0 p (guard97 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 91 (some 113))
  have normalized := agree267 _ _ (change_representative support p 91 (some 113) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check97 (p : Pattern) : (!pushGuard support p 69 91 113 113 || decide (bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder 113 - Generated.soko2_2Potential.boulder 91 + bonus 91 (change p 91 (some 113)))) = true :=
  check_of_implication _ _ (bound97 p)
theorem guard98 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 70 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound98 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 70 .east = true) : bonus 69 p ≤ bonus 70 p := by
  have certified := compare0 p (guard98 p guard)
  simpa only [at69, at70, Int.zero_add] using certified
theorem check98 (p : Pattern) : (!walkGuard soko2_2.board support p 69 70 .east || decide (bonus 69 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound98 p)
theorem guard99 (p : Pattern) (guard : pushGuard support p 69 70 71 71 = true) : d4042 p = 1 := by
  change (!false && (!false || false) && !(p 71) && (!(p 71) || false)) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound99 (p : Pattern) (guard : pushGuard support p 69 70 71 71 = true) : bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder 71 - Generated.soko2_2Potential.boulder 70 + bonus 70 (change p 70 (some 71)) := by
  have certified := compare1005 p (guard99 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 70 (some 71))
  have normalized := agree267 _ _ (change_representative support p 70 (some 71) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 (some 71))
  rw [sub1797]
  exact certified
theorem check99 (p : Pattern) : (!pushGuard support p 69 70 71 71 || decide (bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder 71 - Generated.soko2_2Potential.boulder 70 + bonus 70 (change p 70 (some 71)))) = true :=
  check_of_implication _ _ (bound99 p)
theorem guard100 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 48 .northEast = true) : d4038 p = 1 := by
  change (!false && !(p 48) && !(true && false && false)) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound100 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 48 .northEast = true) : bonus 69 p ≤ bonus 48 p := by
  have certified := compare4 p (guard100 p guard)
  simpa only [at69, at48, Int.zero_add] using certified
theorem check100 (p : Pattern) : (!walkGuard soko2_2.board support p 69 48 .northEast || decide (bonus 69 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound100 p)
theorem guard101 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 46 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound101 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 46 .northWest = true) : bonus 69 p ≤ bonus 46 p := by
  have certified := compare0 p (guard101 p guard)
  simpa only [at69, at46, Int.zero_add] using certified
theorem check101 (p : Pattern) : (!walkGuard soko2_2.board support p 69 46 .northWest || decide (bonus 69 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound101 p)
theorem guard102 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 90 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound102 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 90 .southWest = true) : bonus 69 p ≤ bonus 90 p := by
  have certified := compare0 p (guard102 p guard)
  simpa only [at69, at90, Int.zero_add] using certified
theorem check102 (p : Pattern) : (!walkGuard soko2_2.board support p 69 90 .southWest || decide (bonus 69 p ≤ bonus 90 p)) = true :=
  check_of_implication _ _ (bound102 p)
theorem guard103 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 48 .north = true) : d4038 p = 1 := by
  change (!false && !(p 48) && !false) = true at guard
  cases h48 : p 48
  all_goals simp [d0, d1, d4038, h48] at guard ⊢
theorem bound103 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 48 .north = true) : bonus 70 p ≤ bonus 48 p := by
  have certified := compare4 p (guard103 p guard)
  simpa only [at70, at48, Int.zero_add] using certified
theorem check103 (p : Pattern) : (!walkGuard soko2_2.board support p 70 48 .north || decide (bonus 70 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound103 p)
theorem guard104 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 71 .east = true) : d4042 p = 1 := by
  change (!false && !(p 71) && !false) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound104 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 71 .east = true) : bonus 70 p ≤ bonus 71 p := by
  have certified := compare1011 p (guard104 p guard)
  simpa only [at70, at71, Int.zero_add] using certified
theorem check104 (p : Pattern) : (!walkGuard soko2_2.board support p 70 71 .east || decide (bonus 70 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound104 p)
theorem guard105 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 69 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound105 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 69 .west = true) : bonus 70 p ≤ bonus 69 p := by
  have certified := compare0 p (guard105 p guard)
  simpa only [at70, at69, Int.zero_add] using certified
theorem check105 (p : Pattern) : (!walkGuard soko2_2.board support p 70 69 .west || decide (bonus 70 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound105 p)
theorem guard106 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 49 .northEast = true) : d4052 p = 1 := by
  change (!false && !(p 49) && !(true && (p 48) && (p 71))) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4040, d4042, d4048, d4052, h48, h49, h71] at guard ⊢
theorem bound106 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 49 .northEast = true) : bonus 70 p ≤ bonus 49 p := by
  have certified := compare1016 p (guard106 p guard)
  simpa only [at70, at49, Int.zero_add] using certified
theorem check106 (p : Pattern) : (!walkGuard soko2_2.board support p 70 49 .northEast || decide (bonus 70 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound106 p)
theorem guard107 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 47 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 48) && false)) = true at guard
  cases h48 : p 48
  all_goals simp [d1, h48] at guard ⊢
theorem bound107 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 47 .northWest = true) : bonus 70 p ≤ bonus 47 p := by
  have certified := compare0 p (guard107 p guard)
  simpa only [at70, at47, Int.zero_add] using certified
theorem check107 (p : Pattern) : (!walkGuard soko2_2.board support p 70 47 .northWest || decide (bonus 70 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound107 p)
theorem guard108 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 93 .southEast = true) : d4042 p = 1 := by
  change (!false && !false && !(true && true && (p 71))) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound108 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 93 .southEast = true) : bonus 70 p ≤ bonus 93 p := by
  have certified := compare1021 p (guard108 p guard)
  simpa only [at70, at93, Int.zero_add] using certified
theorem check108 (p : Pattern) : (!walkGuard soko2_2.board support p 70 93 .southEast || decide (bonus 70 p ≤ bonus 93 p)) = true :=
  check_of_implication _ _ (bound108 p)
theorem guard109 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 91 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound109 (p : Pattern) (guard : walkGuard soko2_2.board support p 70 91 .southWest = true) : bonus 70 p ≤ bonus 91 p := by
  have certified := compare0 p (guard109 p guard)
  simpa only [at70, at91, Int.zero_add] using certified
theorem check109 (p : Pattern) : (!walkGuard soko2_2.board support p 70 91 .southWest || decide (bonus 70 p ≤ bonus 91 p)) = true :=
  check_of_implication _ _ (bound109 p)
theorem guard110 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 49 .north = true) : d4048 p = 1 := by
  change (!(p 71) && !(p 49) && !false) = true at guard
  cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4042, d4048, h49, h71] at guard ⊢
theorem bound110 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 49 .north = true) : bonus 71 p ≤ bonus 49 p := by
  have certified := compare1028 p (guard110 p guard)
  simpa only [at71, at49, Int.zero_add] using certified
theorem check110 (p : Pattern) : (!walkGuard soko2_2.board support p 71 49 .north || decide (bonus 71 p ≤ bonus 49 p)) = true :=
  check_of_implication _ _ (bound110 p)
theorem guard111 (p : Pattern) (guard : pushGuard support p 71 49 27 27 = true) : d4043 p = 1 := by
  change (!(p 71) && (!true || (p 49)) && !false && (!false || false)) = true at guard
  cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4042, d4043, h49, h71] at guard ⊢
theorem bound111 (p : Pattern) (guard : pushGuard support p 71 49 27 27 = true) : bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder 27 - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some 27)) := by
  have certified := compare1036 p (guard111 p guard)
  change d488 p ≤ (1 : Int) + d484 (change p 49 (some 27))
  have normalized := agree484 _ _ (change_representative support p 49 (some 27) 10000 dummy_outside)
  rw [normalized]
  change d488 p ≤ (1 : Int) + d484 (change p 49 none)
  rw [sub930]
  exact certified
theorem check111 (p : Pattern) : (!pushGuard support p 71 49 27 27 || decide (bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder 27 - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some 27)))) = true :=
  check_of_implication _ _ (bound111 p)
theorem guard112 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 93 .south = true) : d4042 p = 1 := by
  change (!(p 71) && !false && !false) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound112 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 93 .south = true) : bonus 71 p ≤ bonus 93 p := by
  have certified := compare1043 p (guard112 p guard)
  simpa only [at71, at93, Int.zero_add] using certified
theorem check112 (p : Pattern) : (!walkGuard soko2_2.board support p 71 93 .south || decide (bonus 71 p ≤ bonus 93 p)) = true :=
  check_of_implication _ _ (bound112 p)
theorem guard113 (p : Pattern) (guard : pushGuard support p 71 93 115 115 = true) : d4059 p = 1 := by
  change (!(p 71) && (!false || false) && !(p 115) && (!(p 115) || false)) = true at guard
  cases h71 : p 71 <;> cases h115 : p 115
  all_goals simp [d0, d1, d4058, d4059, h71, h115] at guard ⊢
theorem bound113 (p : Pattern) (guard : pushGuard support p 71 93 115 115 = true) : bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder 115 - Generated.soko2_2Potential.boulder 93 + bonus 93 (change p 93 (some 115)) := by
  have certified := compare1063 p (guard113 p guard)
  change d488 p ≤ (0 : Int) + d312 (change p 93 (some 115))
  have normalized := agree312 _ _ (change_representative support p 93 (some 115) 10000 dummy_outside)
  rw [normalized]
  change d488 p ≤ (0 : Int) + d312 (change p 10000 (some 115))
  rw [sub1999]
  exact certified
theorem check113 (p : Pattern) : (!pushGuard support p 71 93 115 115 || decide (bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder 115 - Generated.soko2_2Potential.boulder 93 + bonus 93 (change p 93 (some 115)))) = true :=
  check_of_implication _ _ (bound113 p)
theorem guard114 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 70 .west = true) : d4042 p = 1 := by
  change (!(p 71) && !false && !false) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound114 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 70 .west = true) : bonus 71 p ≤ bonus 70 p := by
  have certified := compare1069 p (guard114 p guard)
  simpa only [at71, at70, Int.zero_add] using certified
theorem check114 (p : Pattern) : (!walkGuard soko2_2.board support p 71 70 .west || decide (bonus 71 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound114 p)
theorem guard115 (p : Pattern) (guard : pushGuard support p 71 70 69 69 = true) : d4042 p = 1 := by
  change (!(p 71) && (!false || false) && !false && (!false || false)) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound115 (p : Pattern) (guard : pushGuard support p 71 70 69 69 = true) : bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder 69 - Generated.soko2_2Potential.boulder 70 + bonus 70 (change p 70 (some 69)) := by
  have certified := compare1078 p (guard115 p guard)
  change d488 p ≤ (1 : Int) + d267 (change p 70 (some 69))
  have normalized := agree267 _ _ (change_representative support p 70 (some 69) 10000 dummy_outside)
  rw [normalized]
  change d488 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check115 (p : Pattern) : (!pushGuard support p 71 70 69 69 || decide (bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder 69 - Generated.soko2_2Potential.boulder 70 + bonus 70 (change p 70 (some 69)))) = true :=
  check_of_implication _ _ (bound115 p)
theorem guard116 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 50 .northEast = true) : d4048 p = 1 := by
  change (!(p 71) && !false && !(true && (p 49) && true)) = true at guard
  cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4042, d4048, h49, h71] at guard ⊢
theorem bound116 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 50 .northEast = true) : bonus 71 p ≤ bonus 50 p := by
  have certified := compare1083 p (guard116 p guard)
  simpa only [at71, at50, Int.zero_add] using certified
theorem check116 (p : Pattern) : (!walkGuard soko2_2.board support p 71 50 .northEast || decide (bonus 71 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound116 p)
theorem guard117 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 48 .northWest = true) : d4047 p = 1 := by
  change (!(p 71) && !(p 48) && !(true && (p 49) && false)) = true at guard
  cases h48 : p 48 <;> cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4042, d4047, h48, h49, h71] at guard ⊢
theorem bound117 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 48 .northWest = true) : bonus 71 p ≤ bonus 48 p := by
  have certified := compare1085 p (guard117 p guard)
  simpa only [at71, at48, Int.zero_add] using certified
theorem check117 (p : Pattern) : (!walkGuard soko2_2.board support p 71 48 .northWest || decide (bonus 71 p ≤ bonus 48 p)) = true :=
  check_of_implication _ _ (bound117 p)
theorem guard118 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 94 .southEast = true) : d4042 p = 1 := by
  change (!(p 71) && !false && !(true && false && true)) = true at guard
  cases h71 : p 71
  all_goals simp [d0, d1, d4042, h71] at guard ⊢
theorem bound118 (p : Pattern) (guard : walkGuard soko2_2.board support p 71 94 .southEast = true) : bonus 71 p ≤ bonus 94 p := by
  have certified := compare1043 p (guard118 p guard)
  simpa only [at71, at94, Int.zero_add] using certified
theorem check118 (p : Pattern) : (!walkGuard soko2_2.board support p 71 94 .southEast || decide (bonus 71 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound118 p)
theorem guard119 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 51 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound119 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 51 .north = true) : bonus 73 p ≤ bonus 51 p := by
  have certified := compare19 p (guard119 p guard)
  simpa only [at73, at51, Int.zero_add] using certified
theorem check119 (p : Pattern) : (!walkGuard soko2_2.board support p 73 51 .north || decide (bonus 73 p ≤ bonus 51 p)) = true :=
  check_of_implication _ _ (bound119 p)
end NetHack.Sokoban22Refined85
