import NetHack.Sokoban22Refined85.ActionBounds028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard696 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 148 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound696 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 148 .north = true) : bonus 170 p ≤ bonus 148 p := by
  have certified := compare1086 p (guard696 p guard)
  simpa only [at170, at148, Int.zero_add] using certified
theorem check696 (p : Pattern) : (!walkGuard soko2_2.board support p 170 148 .north || decide (bonus 170 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound696 p)
theorem guard697 (p : Pattern) (guard : pushGuard support p 170 148 126 126 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound697 (p : Pattern) (guard : pushGuard support p 170 148 126 126 = true) : bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some 126)) := by
  have certified := compare1087 p (guard697 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 148 (some 126))
  have normalized := agree0 _ _ (change_representative support p 148 (some 126) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check697 (p : Pattern) : (!pushGuard support p 170 148 126 126 || decide (bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some 126)))) = true :=
  check_of_implication _ _ (bound697 p)
theorem guard698 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 192 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound698 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 192 .south = true) : bonus 170 p ≤ bonus 192 p := by
  have certified := compare1086 p (guard698 p guard)
  simpa only [at170, at192, Int.zero_add] using certified
theorem check698 (p : Pattern) : (!walkGuard soko2_2.board support p 170 192 .south || decide (bonus 170 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound698 p)
theorem guard699 (p : Pattern) (guard : pushGuard support p 170 192 214 214 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound699 (p : Pattern) (guard : pushGuard support p 170 192 214 214 = true) : bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder 214 - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some 214)) := by
  have certified := compare1087 p (guard699 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 192 (some 214))
  have normalized := agree0 _ _ (change_representative support p 192 (some 214) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check699 (p : Pattern) : (!pushGuard support p 170 192 214 214 || decide (bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder 214 - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some 214)))) = true :=
  check_of_implication _ _ (bound699 p)
theorem guard700 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 171 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound700 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 171 .east = true) : bonus 170 p ≤ bonus 171 p := by
  have certified := compare1086 p (guard700 p guard)
  simpa only [at170, at171, Int.zero_add] using certified
theorem check700 (p : Pattern) : (!walkGuard soko2_2.board support p 170 171 .east || decide (bonus 170 p ≤ bonus 171 p)) = true :=
  check_of_implication _ _ (bound700 p)
theorem guard701 (p : Pattern) (guard : pushGuard support p 170 171 172 172 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound701 (p : Pattern) (guard : pushGuard support p 170 171 172 172 = true) : bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder 172 - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some 172)) := by
  have certified := compare1087 p (guard701 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 171 (some 172))
  have normalized := agree0 _ _ (change_representative support p 171 (some 172) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check701 (p : Pattern) : (!pushGuard support p 170 171 172 172 || decide (bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder 172 - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some 172)))) = true :=
  check_of_implication _ _ (bound701 p)
theorem guard702 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 169 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound702 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 169 .west = true) : bonus 170 p ≤ bonus 169 p := by
  have certified := compare1086 p (guard702 p guard)
  simpa only [at170, at169, Int.zero_add] using certified
theorem check702 (p : Pattern) : (!walkGuard soko2_2.board support p 170 169 .west || decide (bonus 170 p ≤ bonus 169 p)) = true :=
  check_of_implication _ _ (bound702 p)
theorem guard703 (p : Pattern) (guard : pushGuard support p 170 169 168 168 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound703 (p : Pattern) (guard : pushGuard support p 170 169 168 168 = true) : bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some 168)) := by
  have certified := compare1087 p (guard703 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 169 (some 168))
  have normalized := agree0 _ _ (change_representative support p 169 (some 168) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check703 (p : Pattern) : (!pushGuard support p 170 169 168 168 || decide (bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some 168)))) = true :=
  check_of_implication _ _ (bound703 p)
theorem guard704 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 149 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound704 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 149 .northEast = true) : bonus 170 p ≤ bonus 149 p := by
  have certified := compare1086 p (guard704 p guard)
  simpa only [at170, at149, Int.zero_add] using certified
theorem check704 (p : Pattern) : (!walkGuard soko2_2.board support p 170 149 .northEast || decide (bonus 170 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound704 p)
theorem guard705 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 147 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound705 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 147 .northWest = true) : bonus 170 p ≤ bonus 147 p := by
  have certified := compare1086 p (guard705 p guard)
  simpa only [at170, at147, Int.zero_add] using certified
theorem check705 (p : Pattern) : (!walkGuard soko2_2.board support p 170 147 .northWest || decide (bonus 170 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound705 p)
theorem guard706 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 193 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound706 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 193 .southEast = true) : bonus 170 p ≤ bonus 193 p := by
  have certified := compare1086 p (guard706 p guard)
  simpa only [at170, at193, Int.zero_add] using certified
theorem check706 (p : Pattern) : (!walkGuard soko2_2.board support p 170 193 .southEast || decide (bonus 170 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound706 p)
theorem guard707 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 191 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound707 (p : Pattern) (guard : walkGuard soko2_2.board support p 170 191 .southWest = true) : bonus 170 p ≤ bonus 191 p := by
  have certified := compare1086 p (guard707 p guard)
  simpa only [at170, at191, Int.zero_add] using certified
theorem check707 (p : Pattern) : (!walkGuard soko2_2.board support p 170 191 .southWest || decide (bonus 170 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound707 p)
theorem guard708 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 149 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound708 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 149 .north = true) : bonus 171 p ≤ bonus 149 p := by
  have certified := compare1086 p (guard708 p guard)
  simpa only [at171, at149, Int.zero_add] using certified
theorem check708 (p : Pattern) : (!walkGuard soko2_2.board support p 171 149 .north || decide (bonus 171 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound708 p)
theorem guard709 (p : Pattern) (guard : pushGuard support p 171 149 127 127 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound709 (p : Pattern) (guard : pushGuard support p 171 149 127 127 = true) : bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some 127)) := by
  have certified := compare1087 p (guard709 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 149 (some 127))
  have normalized := agree0 _ _ (change_representative support p 149 (some 127) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check709 (p : Pattern) : (!pushGuard support p 171 149 127 127 || decide (bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some 127)))) = true :=
  check_of_implication _ _ (bound709 p)
theorem guard710 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 193 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound710 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 193 .south = true) : bonus 171 p ≤ bonus 193 p := by
  have certified := compare1086 p (guard710 p guard)
  simpa only [at171, at193, Int.zero_add] using certified
theorem check710 (p : Pattern) : (!walkGuard soko2_2.board support p 171 193 .south || decide (bonus 171 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound710 p)
theorem guard711 (p : Pattern) (guard : pushGuard support p 171 193 215 215 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound711 (p : Pattern) (guard : pushGuard support p 171 193 215 215 = true) : bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder 215 - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some 215)) := by
  have certified := compare1087 p (guard711 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 193 (some 215))
  have normalized := agree0 _ _ (change_representative support p 193 (some 215) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check711 (p : Pattern) : (!pushGuard support p 171 193 215 215 || decide (bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder 215 - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some 215)))) = true :=
  check_of_implication _ _ (bound711 p)
theorem guard712 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 172 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound712 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 172 .east = true) : bonus 171 p ≤ bonus 172 p := by
  have certified := compare1086 p (guard712 p guard)
  simpa only [at171, at172, Int.zero_add] using certified
theorem check712 (p : Pattern) : (!walkGuard soko2_2.board support p 171 172 .east || decide (bonus 171 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound712 p)
theorem guard713 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 170 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound713 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 170 .west = true) : bonus 171 p ≤ bonus 170 p := by
  have certified := compare1086 p (guard713 p guard)
  simpa only [at171, at170, Int.zero_add] using certified
theorem check713 (p : Pattern) : (!walkGuard soko2_2.board support p 171 170 .west || decide (bonus 171 p ≤ bonus 170 p)) = true :=
  check_of_implication _ _ (bound713 p)
theorem guard714 (p : Pattern) (guard : pushGuard support p 171 170 169 169 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound714 (p : Pattern) (guard : pushGuard support p 171 170 169 169 = true) : bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some 169)) := by
  have certified := compare1087 p (guard714 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 170 (some 169))
  have normalized := agree0 _ _ (change_representative support p 170 (some 169) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check714 (p : Pattern) : (!pushGuard support p 171 170 169 169 || decide (bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some 169)))) = true :=
  check_of_implication _ _ (bound714 p)
theorem guard715 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 150 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound715 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 150 .northEast = true) : bonus 171 p ≤ bonus 150 p := by
  have certified := compare1086 p (guard715 p guard)
  simpa only [at171, at150, Int.zero_add] using certified
theorem check715 (p : Pattern) : (!walkGuard soko2_2.board support p 171 150 .northEast || decide (bonus 171 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound715 p)
theorem guard716 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 148 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound716 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 148 .northWest = true) : bonus 171 p ≤ bonus 148 p := by
  have certified := compare1086 p (guard716 p guard)
  simpa only [at171, at148, Int.zero_add] using certified
theorem check716 (p : Pattern) : (!walkGuard soko2_2.board support p 171 148 .northWest || decide (bonus 171 p ≤ bonus 148 p)) = true :=
  check_of_implication _ _ (bound716 p)
theorem guard717 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 194 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound717 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 194 .southEast = true) : bonus 171 p ≤ bonus 194 p := by
  have certified := compare1086 p (guard717 p guard)
  simpa only [at171, at194, Int.zero_add] using certified
theorem check717 (p : Pattern) : (!walkGuard soko2_2.board support p 171 194 .southEast || decide (bonus 171 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound717 p)
theorem guard718 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 192 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound718 (p : Pattern) (guard : walkGuard soko2_2.board support p 171 192 .southWest = true) : bonus 171 p ≤ bonus 192 p := by
  have certified := compare1086 p (guard718 p guard)
  simpa only [at171, at192, Int.zero_add] using certified
theorem check718 (p : Pattern) : (!walkGuard soko2_2.board support p 171 192 .southWest || decide (bonus 171 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound718 p)
theorem guard719 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 150 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound719 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 150 .north = true) : bonus 172 p ≤ bonus 150 p := by
  have certified := compare1086 p (guard719 p guard)
  simpa only [at172, at150, Int.zero_add] using certified
theorem check719 (p : Pattern) : (!walkGuard soko2_2.board support p 172 150 .north || decide (bonus 172 p ≤ bonus 150 p)) = true :=
  check_of_implication _ _ (bound719 p)
end NetHack.Sokoban22Refined85
