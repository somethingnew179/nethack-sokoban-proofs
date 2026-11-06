import NetHack.Sokoban22Refined85.ActionBounds002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard72 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 71 .southWest = true) : d4048 p = 1 := by
  change (!false && !(p 71) && !(true && true && (p 49))) = true at guard
  cases h49 : p 49 <;> cases h71 : p 71
  all_goals simp [d0, d1, d4042, d4048, h49, h71] at guard ⊢
theorem bound72 (p : Pattern) (guard : walkGuard soko2_2.board support p 50 71 .southWest = true) : bonus 50 p ≤ bonus 71 p := by
  have certified := compare580 p (guard72 p guard)
  simpa only [at50, at71, Int.zero_add] using certified
theorem check72 (p : Pattern) : (!walkGuard soko2_2.board support p 50 71 .southWest || decide (bonus 50 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound72 p)
theorem guard73 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 29 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound73 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 29 .north = true) : bonus 51 p ≤ bonus 29 p := by
  have certified := compare19 p (guard73 p guard)
  simpa only [at51, at29, Int.zero_add] using certified
theorem check73 (p : Pattern) : (!walkGuard soko2_2.board support p 51 29 .north || decide (bonus 51 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound73 p)
theorem guard74 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 73 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound74 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 73 .south = true) : bonus 51 p ≤ bonus 73 p := by
  have certified := compare19 p (guard74 p guard)
  simpa only [at51, at73, Int.zero_add] using certified
theorem check74 (p : Pattern) : (!walkGuard soko2_2.board support p 51 73 .south || decide (bonus 51 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound74 p)
theorem guard75 (p : Pattern) (guard : pushGuard support p 51 73 95 95 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound75 (p : Pattern) (guard : pushGuard support p 51 73 95 95 = true) : bonus 51 p ≤ 1 + Generated.soko2_2Potential.boulder 95 - Generated.soko2_2Potential.boulder 73 + bonus 73 (change p 73 (some 95)) := by
  have certified := compare20 p (guard75 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 73 (some 95))
  have normalized := agree312 _ _ (change_representative support p 73 (some 95) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check75 (p : Pattern) : (!pushGuard support p 51 73 95 95 || decide (bonus 51 p ≤ 1 + Generated.soko2_2Potential.boulder 95 - Generated.soko2_2Potential.boulder 73 + bonus 73 (change p 73 (some 95)))) = true :=
  check_of_implication _ _ (bound75 p)
theorem guard76 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 52 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound76 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 52 .east = true) : bonus 51 p ≤ bonus 52 p := by
  have certified := compare19 p (guard76 p guard)
  simpa only [at51, at52, Int.zero_add] using certified
theorem check76 (p : Pattern) : (!walkGuard soko2_2.board support p 51 52 .east || decide (bonus 51 p ≤ bonus 52 p)) = true :=
  check_of_implication _ _ (bound76 p)
theorem guard77 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 50 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound77 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 50 .west = true) : bonus 51 p ≤ bonus 50 p := by
  have certified := compare19 p (guard77 p guard)
  simpa only [at51, at50, Int.zero_add] using certified
theorem check77 (p : Pattern) : (!walkGuard soko2_2.board support p 51 50 .west || decide (bonus 51 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound77 p)
theorem guard78 (p : Pattern) (guard : pushGuard support p 51 50 49 49 = true) : d4040 p = 1 := by
  change (!false && (!false || false) && !(p 49) && (!(p 49) || false)) = true at guard
  cases h49 : p 49
  all_goals simp [d0, d1, d4040, h49] at guard ⊢
theorem bound78 (p : Pattern) (guard : pushGuard support p 51 50 49 49 = true) : bonus 51 p ≤ 1 + Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.boulder 50 + bonus 50 (change p 50 (some 49)) := by
  have certified := compare675 p (guard78 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 50 (some 49))
  have normalized := agree312 _ _ (change_representative support p 50 (some 49) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 (some 49))
  rw [sub1529]
  exact certified
theorem check78 (p : Pattern) : (!pushGuard support p 51 50 49 49 || decide (bonus 51 p ≤ 1 + Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.boulder 50 + bonus 50 (change p 50 (some 49)))) = true :=
  check_of_implication _ _ (bound78 p)
theorem guard79 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 30 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound79 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 30 .northEast = true) : bonus 51 p ≤ bonus 30 p := by
  have certified := compare19 p (guard79 p guard)
  simpa only [at51, at30, Int.zero_add] using certified
theorem check79 (p : Pattern) : (!walkGuard soko2_2.board support p 51 30 .northEast || decide (bonus 51 p ≤ bonus 30 p)) = true :=
  check_of_implication _ _ (bound79 p)
theorem guard80 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 28 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound80 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 28 .northWest = true) : bonus 51 p ≤ bonus 28 p := by
  have certified := compare19 p (guard80 p guard)
  simpa only [at51, at28, Int.zero_add] using certified
theorem check80 (p : Pattern) : (!walkGuard soko2_2.board support p 51 28 .northWest || decide (bonus 51 p ≤ bonus 28 p)) = true :=
  check_of_implication _ _ (bound80 p)
theorem guard81 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 74 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound81 (p : Pattern) (guard : walkGuard soko2_2.board support p 51 74 .southEast = true) : bonus 51 p ≤ bonus 74 p := by
  have certified := compare19 p (guard81 p guard)
  simpa only [at51, at74, Int.zero_add] using certified
theorem check81 (p : Pattern) : (!walkGuard soko2_2.board support p 51 74 .southEast || decide (bonus 51 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound81 p)
theorem guard82 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 30 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound82 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 30 .north = true) : bonus 52 p ≤ bonus 30 p := by
  have certified := compare19 p (guard82 p guard)
  simpa only [at52, at30, Int.zero_add] using certified
theorem check82 (p : Pattern) : (!walkGuard soko2_2.board support p 52 30 .north || decide (bonus 52 p ≤ bonus 30 p)) = true :=
  check_of_implication _ _ (bound82 p)
theorem guard83 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 74 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound83 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 74 .south = true) : bonus 52 p ≤ bonus 74 p := by
  have certified := compare19 p (guard83 p guard)
  simpa only [at52, at74, Int.zero_add] using certified
theorem check83 (p : Pattern) : (!walkGuard soko2_2.board support p 52 74 .south || decide (bonus 52 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound83 p)
theorem guard84 (p : Pattern) (guard : pushGuard support p 52 74 96 96 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound84 (p : Pattern) (guard : pushGuard support p 52 74 96 96 = true) : bonus 52 p ≤ 1 + Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.boulder 74 + bonus 74 (change p 74 (some 96)) := by
  have certified := compare20 p (guard84 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 74 (some 96))
  have normalized := agree312 _ _ (change_representative support p 74 (some 96) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check84 (p : Pattern) : (!pushGuard support p 52 74 96 96 || decide (bonus 52 p ≤ 1 + Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.boulder 74 + bonus 74 (change p 74 (some 96)))) = true :=
  check_of_implication _ _ (bound84 p)
theorem guard85 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 51 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound85 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 51 .west = true) : bonus 52 p ≤ bonus 51 p := by
  have certified := compare19 p (guard85 p guard)
  simpa only [at52, at51, Int.zero_add] using certified
theorem check85 (p : Pattern) : (!walkGuard soko2_2.board support p 52 51 .west || decide (bonus 52 p ≤ bonus 51 p)) = true :=
  check_of_implication _ _ (bound85 p)
theorem guard86 (p : Pattern) (guard : pushGuard support p 52 51 50 50 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound86 (p : Pattern) (guard : pushGuard support p 52 51 50 50 = true) : bonus 52 p ≤ 1 + Generated.soko2_2Potential.boulder 50 - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some 50)) := by
  have certified := compare20 p (guard86 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 51 (some 50))
  have normalized := agree312 _ _ (change_representative support p 51 (some 50) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check86 (p : Pattern) : (!pushGuard support p 52 51 50 50 || decide (bonus 52 p ≤ 1 + Generated.soko2_2Potential.boulder 50 - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some 50)))) = true :=
  check_of_implication _ _ (bound86 p)
theorem guard87 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 29 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound87 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 29 .northWest = true) : bonus 52 p ≤ bonus 29 p := by
  have certified := compare19 p (guard87 p guard)
  simpa only [at52, at29, Int.zero_add] using certified
theorem check87 (p : Pattern) : (!walkGuard soko2_2.board support p 52 29 .northWest || decide (bonus 52 p ≤ bonus 29 p)) = true :=
  check_of_implication _ _ (bound87 p)
theorem guard88 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 73 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound88 (p : Pattern) (guard : walkGuard soko2_2.board support p 52 73 .southWest = true) : bonus 52 p ≤ bonus 73 p := by
  have certified := compare19 p (guard88 p guard)
  simpa only [at52, at73, Int.zero_add] using certified
theorem check88 (p : Pattern) : (!walkGuard soko2_2.board support p 52 73 .southWest || decide (bonus 52 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound88 p)
theorem guard89 (p : Pattern) (guard : walkGuard soko2_2.board support p 67 45 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound89 (p : Pattern) (guard : walkGuard soko2_2.board support p 67 45 .north = true) : bonus 67 p ≤ bonus 45 p := by
  have certified := compare0 p (guard89 p guard)
  simpa only [at67, at45, Int.zero_add] using certified
theorem check89 (p : Pattern) : (!walkGuard soko2_2.board support p 67 45 .north || decide (bonus 67 p ≤ bonus 45 p)) = true :=
  check_of_implication _ _ (bound89 p)
theorem guard90 (p : Pattern) (guard : walkGuard soko2_2.board support p 67 89 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound90 (p : Pattern) (guard : walkGuard soko2_2.board support p 67 89 .south = true) : bonus 67 p ≤ bonus 89 p := by
  have certified := compare0 p (guard90 p guard)
  simpa only [at67, at89, Int.zero_add] using certified
theorem check90 (p : Pattern) : (!walkGuard soko2_2.board support p 67 89 .south || decide (bonus 67 p ≤ bonus 89 p)) = true :=
  check_of_implication _ _ (bound90 p)
theorem guard91 (p : Pattern) (guard : pushGuard support p 67 89 111 111 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound91 (p : Pattern) (guard : pushGuard support p 67 89 111 111 = true) : bonus 67 p ≤ 1 + Generated.soko2_2Potential.boulder 111 - Generated.soko2_2Potential.boulder 89 + bonus 89 (change p 89 (some 111)) := by
  have certified := compare1 p (guard91 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 89 (some 111))
  have normalized := agree267 _ _ (change_representative support p 89 (some 111) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check91 (p : Pattern) : (!pushGuard support p 67 89 111 111 || decide (bonus 67 p ≤ 1 + Generated.soko2_2Potential.boulder 111 - Generated.soko2_2Potential.boulder 89 + bonus 89 (change p 89 (some 111)))) = true :=
  check_of_implication _ _ (bound91 p)
theorem guard92 (p : Pattern) (guard : walkGuard soko2_2.board support p 67 46 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound92 (p : Pattern) (guard : walkGuard soko2_2.board support p 67 46 .northEast = true) : bonus 67 p ≤ bonus 46 p := by
  have certified := compare0 p (guard92 p guard)
  simpa only [at67, at46, Int.zero_add] using certified
theorem check92 (p : Pattern) : (!walkGuard soko2_2.board support p 67 46 .northEast || decide (bonus 67 p ≤ bonus 46 p)) = true :=
  check_of_implication _ _ (bound92 p)
theorem guard93 (p : Pattern) (guard : walkGuard soko2_2.board support p 67 90 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound93 (p : Pattern) (guard : walkGuard soko2_2.board support p 67 90 .southEast = true) : bonus 67 p ≤ bonus 90 p := by
  have certified := compare0 p (guard93 p guard)
  simpa only [at67, at90, Int.zero_add] using certified
theorem check93 (p : Pattern) : (!walkGuard soko2_2.board support p 67 90 .southEast || decide (bonus 67 p ≤ bonus 90 p)) = true :=
  check_of_implication _ _ (bound93 p)
theorem guard94 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 47 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound94 (p : Pattern) (guard : walkGuard soko2_2.board support p 69 47 .north = true) : bonus 69 p ≤ bonus 47 p := by
  have certified := compare0 p (guard94 p guard)
  simpa only [at69, at47, Int.zero_add] using certified
theorem check94 (p : Pattern) : (!walkGuard soko2_2.board support p 69 47 .north || decide (bonus 69 p ≤ bonus 47 p)) = true :=
  check_of_implication _ _ (bound94 p)
theorem guard95 (p : Pattern) (guard : pushGuard support p 69 47 25 25 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound95 (p : Pattern) (guard : pushGuard support p 69 47 25 25 = true) : bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder 25 - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some 25)) := by
  have certified := compare1 p (guard95 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 47 (some 25))
  have normalized := agree267 _ _ (change_representative support p 47 (some 25) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check95 (p : Pattern) : (!pushGuard support p 69 47 25 25 || decide (bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder 25 - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some 25)))) = true :=
  check_of_implication _ _ (bound95 p)
end NetHack.Sokoban22Refined85
