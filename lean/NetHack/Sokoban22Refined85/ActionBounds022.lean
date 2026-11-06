import NetHack.Sokoban22Refined85.ActionBounds021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard528 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 125 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound528 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 125 .northEast = true) : bonus 146 p ≤ bonus 125 p := by
  have certified := compare1086 p (guard528 p guard)
  simpa only [at146, at125, Int.zero_add] using certified
theorem check528 (p : Pattern) : (!walkGuard soko2_2.board support p 146 125 .northEast || decide (bonus 146 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound528 p)
theorem guard529 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 123 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound529 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 123 .northWest = true) : bonus 146 p ≤ bonus 123 p := by
  have certified := compare1086 p (guard529 p guard)
  simpa only [at146, at123, Int.zero_add] using certified
theorem check529 (p : Pattern) : (!walkGuard soko2_2.board support p 146 123 .northWest || decide (bonus 146 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound529 p)
theorem guard530 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 169 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound530 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 169 .southEast = true) : bonus 146 p ≤ bonus 169 p := by
  have certified := compare1086 p (guard530 p guard)
  simpa only [at146, at169, Int.zero_add] using certified
theorem check530 (p : Pattern) : (!walkGuard soko2_2.board support p 146 169 .southEast || decide (bonus 146 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound530 p)
theorem guard531 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 167 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound531 (p : Pattern) (guard : walkGuard soko2_2.board support p 146 167 .southWest = true) : bonus 146 p ≤ bonus 167 p := by
  have certified := compare1086 p (guard531 p guard)
  simpa only [at146, at167, Int.zero_add] using certified
theorem check531 (p : Pattern) : (!walkGuard soko2_2.board support p 146 167 .southWest || decide (bonus 146 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound531 p)
theorem guard532 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 125 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound532 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 125 .north = true) : bonus 147 p ≤ bonus 125 p := by
  have certified := compare1086 p (guard532 p guard)
  simpa only [at147, at125, Int.zero_add] using certified
theorem check532 (p : Pattern) : (!walkGuard soko2_2.board support p 147 125 .north || decide (bonus 147 p ≤ bonus 125 p)) = true :=
  check_of_implication _ _ (bound532 p)
theorem guard533 (p : Pattern) (guard : pushGuard support p 147 125 103 103 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound533 (p : Pattern) (guard : pushGuard support p 147 125 103 103 = true) : bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some 103)) := by
  have certified := compare1087 p (guard533 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 125 (some 103))
  have normalized := agree0 _ _ (change_representative support p 125 (some 103) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check533 (p : Pattern) : (!pushGuard support p 147 125 103 103 || decide (bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some 103)))) = true :=
  check_of_implication _ _ (bound533 p)
theorem guard534 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 169 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound534 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 169 .south = true) : bonus 147 p ≤ bonus 169 p := by
  have certified := compare1086 p (guard534 p guard)
  simpa only [at147, at169, Int.zero_add] using certified
theorem check534 (p : Pattern) : (!walkGuard soko2_2.board support p 147 169 .south || decide (bonus 147 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound534 p)
theorem guard535 (p : Pattern) (guard : pushGuard support p 147 169 191 191 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound535 (p : Pattern) (guard : pushGuard support p 147 169 191 191 = true) : bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some 191)) := by
  have certified := compare1087 p (guard535 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 169 (some 191))
  have normalized := agree0 _ _ (change_representative support p 169 (some 191) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check535 (p : Pattern) : (!pushGuard support p 147 169 191 191 || decide (bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some 191)))) = true :=
  check_of_implication _ _ (bound535 p)
theorem guard536 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 148 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound536 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 148 .east = true) : bonus 147 p ≤ bonus 148 p := by
  have certified := compare1086 p (guard536 p guard)
  simpa only [at147, at148, Int.zero_add] using certified
theorem check536 (p : Pattern) : (!walkGuard soko2_2.board support p 147 148 .east || decide (bonus 147 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound536 p)
theorem guard537 (p : Pattern) (guard : pushGuard support p 147 148 149 149 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound537 (p : Pattern) (guard : pushGuard support p 147 148 149 149 = true) : bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some 149)) := by
  have certified := compare1087 p (guard537 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 148 (some 149))
  have normalized := agree0 _ _ (change_representative support p 148 (some 149) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check537 (p : Pattern) : (!pushGuard support p 147 148 149 149 || decide (bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some 149)))) = true :=
  check_of_implication _ _ (bound537 p)
theorem guard538 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 146 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound538 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 146 .west = true) : bonus 147 p ≤ bonus 146 p := by
  have certified := compare1086 p (guard538 p guard)
  simpa only [at147, at146, Int.zero_add] using certified
theorem check538 (p : Pattern) : (!walkGuard soko2_2.board support p 147 146 .west || decide (bonus 147 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound538 p)
theorem guard539 (p : Pattern) (guard : pushGuard support p 147 146 145 145 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound539 (p : Pattern) (guard : pushGuard support p 147 146 145 145 = true) : bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some 145)) := by
  have certified := compare1087 p (guard539 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 146 (some 145))
  have normalized := agree0 _ _ (change_representative support p 146 (some 145) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check539 (p : Pattern) : (!pushGuard support p 147 146 145 145 || decide (bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some 145)))) = true :=
  check_of_implication _ _ (bound539 p)
theorem guard540 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 126 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound540 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 126 .northEast = true) : bonus 147 p ≤ bonus 126 p := by
  have certified := compare1086 p (guard540 p guard)
  simpa only [at147, at126, Int.zero_add] using certified
theorem check540 (p : Pattern) : (!walkGuard soko2_2.board support p 147 126 .northEast || decide (bonus 147 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound540 p)
theorem guard541 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 124 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound541 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 124 .northWest = true) : bonus 147 p ≤ bonus 124 p := by
  have certified := compare1086 p (guard541 p guard)
  simpa only [at147, at124, Int.zero_add] using certified
theorem check541 (p : Pattern) : (!walkGuard soko2_2.board support p 147 124 .northWest || decide (bonus 147 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound541 p)
theorem guard542 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 170 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound542 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 170 .southEast = true) : bonus 147 p ≤ bonus 170 p := by
  have certified := compare1086 p (guard542 p guard)
  simpa only [at147, at170, Int.zero_add] using certified
theorem check542 (p : Pattern) : (!walkGuard soko2_2.board support p 147 170 .southEast || decide (bonus 147 p ≤ bonus 170 p)) = true :=
  check_of_implication _ _ (bound542 p)
theorem guard543 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 168 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound543 (p : Pattern) (guard : walkGuard soko2_2.board support p 147 168 .southWest = true) : bonus 147 p ≤ bonus 168 p := by
  have certified := compare1086 p (guard543 p guard)
  simpa only [at147, at168, Int.zero_add] using certified
theorem check543 (p : Pattern) : (!walkGuard soko2_2.board support p 147 168 .southWest || decide (bonus 147 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound543 p)
theorem guard544 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 126 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound544 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 126 .north = true) : bonus 148 p ≤ bonus 126 p := by
  have certified := compare1086 p (guard544 p guard)
  simpa only [at148, at126, Int.zero_add] using certified
theorem check544 (p : Pattern) : (!walkGuard soko2_2.board support p 148 126 .north || decide (bonus 148 p ≤ bonus 126 p)) = true :=
  check_of_implication _ _ (bound544 p)
theorem guard545 (p : Pattern) (guard : pushGuard support p 148 126 104 104 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound545 (p : Pattern) (guard : pushGuard support p 148 126 104 104 = true) : bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some 104)) := by
  have certified := compare1087 p (guard545 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 126 (some 104))
  have normalized := agree0 _ _ (change_representative support p 126 (some 104) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check545 (p : Pattern) : (!pushGuard support p 148 126 104 104 || decide (bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some 104)))) = true :=
  check_of_implication _ _ (bound545 p)
theorem guard546 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 170 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound546 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 170 .south = true) : bonus 148 p ≤ bonus 170 p := by
  have certified := compare1086 p (guard546 p guard)
  simpa only [at148, at170, Int.zero_add] using certified
theorem check546 (p : Pattern) : (!walkGuard soko2_2.board support p 148 170 .south || decide (bonus 148 p ≤ bonus 170 p)) = true :=
  check_of_implication _ _ (bound546 p)
theorem guard547 (p : Pattern) (guard : pushGuard support p 148 170 192 192 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound547 (p : Pattern) (guard : pushGuard support p 148 170 192 192 = true) : bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some 192)) := by
  have certified := compare1087 p (guard547 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 170 (some 192))
  have normalized := agree0 _ _ (change_representative support p 170 (some 192) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check547 (p : Pattern) : (!pushGuard support p 148 170 192 192 || decide (bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some 192)))) = true :=
  check_of_implication _ _ (bound547 p)
theorem guard548 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 149 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound548 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 149 .east = true) : bonus 148 p ≤ bonus 149 p := by
  have certified := compare1086 p (guard548 p guard)
  simpa only [at148, at149, Int.zero_add] using certified
theorem check548 (p : Pattern) : (!walkGuard soko2_2.board support p 148 149 .east || decide (bonus 148 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound548 p)
theorem guard549 (p : Pattern) (guard : pushGuard support p 148 149 150 150 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound549 (p : Pattern) (guard : pushGuard support p 148 149 150 150 = true) : bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder 150 - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some 150)) := by
  have certified := compare1087 p (guard549 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 149 (some 150))
  have normalized := agree0 _ _ (change_representative support p 149 (some 150) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check549 (p : Pattern) : (!pushGuard support p 148 149 150 150 || decide (bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder 150 - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some 150)))) = true :=
  check_of_implication _ _ (bound549 p)
theorem guard550 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 147 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound550 (p : Pattern) (guard : walkGuard soko2_2.board support p 148 147 .west = true) : bonus 148 p ≤ bonus 147 p := by
  have certified := compare1086 p (guard550 p guard)
  simpa only [at148, at147, Int.zero_add] using certified
theorem check550 (p : Pattern) : (!walkGuard soko2_2.board support p 148 147 .west || decide (bonus 148 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound550 p)
theorem guard551 (p : Pattern) (guard : pushGuard support p 148 147 146 146 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound551 (p : Pattern) (guard : pushGuard support p 148 147 146 146 = true) : bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some 146)) := by
  have certified := compare1087 p (guard551 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 147 (some 146))
  have normalized := agree0 _ _ (change_representative support p 147 (some 146) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check551 (p : Pattern) : (!pushGuard support p 148 147 146 146 || decide (bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some 146)))) = true :=
  check_of_implication _ _ (bound551 p)
end NetHack.Sokoban22Refined85
