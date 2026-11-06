import NetHack.Sokoban12CostPartition.ActionBounds020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard504 (p : Pattern) (guard : pushGuard support p 213 239 265 265 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound504 (p : Pattern) (guard : pushGuard support p 213 239 265 265 = true) : bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder 265 - Generated.soko1_2Potential.boulder 239 + bonus 239 (change p 239 (some 265)) := by
  have certified := compare2570 p (guard504 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 239 (some 265))
  have normalized := agree258 _ _ (change_representative support p 239 (some 265) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check504 (p : Pattern) : (!pushGuard support p 213 239 265 265 || decide (bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder 265 - Generated.soko1_2Potential.boulder 239 + bonus 239 (change p 239 (some 265)))) = true :=
  check_of_implication _ _ (bound504 p)
theorem guard505 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 214 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound505 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 214 .east = true) : bonus 213 p ≤ bonus 214 p := by
  have certified := compare897 p (guard505 p guard)
  simpa only [at213, at214, Int.zero_add] using certified
theorem check505 (p : Pattern) : (!walkGuard soko1_2.board support p 213 214 .east || decide (bonus 213 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound505 p)
theorem guard506 (p : Pattern) (guard : pushGuard support p 213 214 215 215 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound506 (p : Pattern) (guard : pushGuard support p 213 214 215 215 = true) : bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder 215 - Generated.soko1_2Potential.boulder 214 + bonus 214 (change p 214 (some 215)) := by
  have certified := compare2570 p (guard506 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 214 (some 215))
  have normalized := agree258 _ _ (change_representative support p 214 (some 215) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check506 (p : Pattern) : (!pushGuard support p 213 214 215 215 || decide (bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder 215 - Generated.soko1_2Potential.boulder 214 + bonus 214 (change p 214 (some 215)))) = true :=
  check_of_implication _ _ (bound506 p)
theorem guard507 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 212 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound507 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 212 .west = true) : bonus 213 p ≤ bonus 212 p := by
  have certified := compare897 p (guard507 p guard)
  simpa only [at213, at212, Int.zero_add] using certified
theorem check507 (p : Pattern) : (!walkGuard soko1_2.board support p 213 212 .west || decide (bonus 213 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound507 p)
theorem guard508 (p : Pattern) (guard : pushGuard support p 213 212 211 211 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound508 (p : Pattern) (guard : pushGuard support p 213 212 211 211 = true) : bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some 211)) := by
  have certified := compare2570 p (guard508 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 212 (some 211))
  have normalized := agree258 _ _ (change_representative support p 212 (some 211) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check508 (p : Pattern) : (!pushGuard support p 213 212 211 211 || decide (bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some 211)))) = true :=
  check_of_implication _ _ (bound508 p)
theorem guard509 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 186 .northWest = true) : d829 p = 1 := by
  change (!false && !(p 186) && !(true && (p 187) && false)) = true at guard
  cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d829, h186, h187] at guard ⊢
theorem bound509 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 186 .northWest = true) : bonus 213 p ≤ bonus 186 p := by
  have certified := compare3692 p (guard509 p guard)
  simpa only [at213, at186, Int.zero_add] using certified
theorem check509 (p : Pattern) : (!walkGuard soko1_2.board support p 213 186 .northWest || decide (bonus 213 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound509 p)
theorem guard510 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 238 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound510 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 238 .southWest = true) : bonus 213 p ≤ bonus 238 p := by
  have certified := compare897 p (guard510 p guard)
  simpa only [at213, at238, Int.zero_add] using certified
theorem check510 (p : Pattern) : (!walkGuard soko1_2.board support p 213 238 .southWest || decide (bonus 213 p ≤ bonus 238 p)) = true :=
  check_of_implication _ _ (bound510 p)
theorem guard511 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 215 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound511 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 215 .east = true) : bonus 214 p ≤ bonus 215 p := by
  have certified := compare897 p (guard511 p guard)
  simpa only [at214, at215, Int.zero_add] using certified
theorem check511 (p : Pattern) : (!walkGuard soko1_2.board support p 214 215 .east || decide (bonus 214 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound511 p)
theorem guard512 (p : Pattern) (guard : pushGuard support p 214 215 216 216 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound512 (p : Pattern) (guard : pushGuard support p 214 215 216 216 = true) : bonus 214 p ≤ 1 + Generated.soko1_2Potential.boulder 216 - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some 216)) := by
  have certified := compare5790 p (guard512 p guard)
  change d258 p ≤ (4 : Int) + d258 (change p 215 (some 216))
  have normalized := agree258 _ _ (change_representative support p 215 (some 216) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (4 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check512 (p : Pattern) : (!pushGuard support p 214 215 216 216 || decide (bonus 214 p ≤ 1 + Generated.soko1_2Potential.boulder 216 - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some 216)))) = true :=
  check_of_implication _ _ (bound512 p)
theorem guard513 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 213 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound513 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 213 .west = true) : bonus 214 p ≤ bonus 213 p := by
  have certified := compare897 p (guard513 p guard)
  simpa only [at214, at213, Int.zero_add] using certified
theorem check513 (p : Pattern) : (!walkGuard soko1_2.board support p 214 213 .west || decide (bonus 214 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound513 p)
theorem guard514 (p : Pattern) (guard : pushGuard support p 214 213 212 212 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound514 (p : Pattern) (guard : pushGuard support p 214 213 212 212 = true) : bonus 214 p ≤ 1 + Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some 212)) := by
  have certified := compare897 p (guard514 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 213 (some 212))
  have normalized := agree258 _ _ (change_representative support p 213 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check514 (p : Pattern) : (!pushGuard support p 214 213 212 212 || decide (bonus 214 p ≤ 1 + Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some 212)))) = true :=
  check_of_implication _ _ (bound514 p)
theorem guard515 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 189 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound515 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 189 .northEast = true) : bonus 214 p ≤ bonus 189 p := by
  have certified := compare897 p (guard515 p guard)
  simpa only [at214, at189, Int.zero_add] using certified
theorem check515 (p : Pattern) : (!walkGuard soko1_2.board support p 214 189 .northEast || decide (bonus 214 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound515 p)
theorem guard516 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 187 .northWest = true) : d851 p = 1 := by
  change (!false && !(p 187) && !(true && true && false)) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound516 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 187 .northWest = true) : bonus 214 p ≤ bonus 187 p := by
  have certified := compare5729 p (guard516 p guard)
  simpa only [at214, at187, Int.zero_add] using certified
theorem check516 (p : Pattern) : (!walkGuard soko1_2.board support p 214 187 .northWest || decide (bonus 214 p ≤ bonus 187 p)) = true :=
  check_of_implication _ _ (bound516 p)
theorem guard517 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 241 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound517 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 241 .southEast = true) : bonus 214 p ≤ bonus 241 p := by
  have certified := compare897 p (guard517 p guard)
  simpa only [at214, at241, Int.zero_add] using certified
theorem check517 (p : Pattern) : (!walkGuard soko1_2.board support p 214 241 .southEast || decide (bonus 214 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound517 p)
theorem guard518 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 239 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound518 (p : Pattern) (guard : walkGuard soko1_2.board support p 214 239 .southWest = true) : bonus 214 p ≤ bonus 239 p := by
  have certified := compare897 p (guard518 p guard)
  simpa only [at214, at239, Int.zero_add] using certified
theorem check518 (p : Pattern) : (!walkGuard soko1_2.board support p 214 239 .southWest || decide (bonus 214 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound518 p)
theorem guard519 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 189 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound519 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 189 .north = true) : bonus 215 p ≤ bonus 189 p := by
  have certified := compare897 p (guard519 p guard)
  simpa only [at215, at189, Int.zero_add] using certified
theorem check519 (p : Pattern) : (!walkGuard soko1_2.board support p 215 189 .north || decide (bonus 215 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound519 p)
theorem guard520 (p : Pattern) (guard : pushGuard support p 215 189 163 163 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound520 (p : Pattern) (guard : pushGuard support p 215 189 163 163 = true) : bonus 215 p ≤ 1 + Generated.soko1_2Potential.boulder 163 - Generated.soko1_2Potential.boulder 189 + bonus 189 (change p 189 (some 163)) := by
  have certified := compare5791 p (guard520 p guard)
  change d258 p ≤ (7 : Int) + d258 (change p 189 (some 163))
  have normalized := agree258 _ _ (change_representative support p 189 (some 163) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (7 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check520 (p : Pattern) : (!pushGuard support p 215 189 163 163 || decide (bonus 215 p ≤ 1 + Generated.soko1_2Potential.boulder 163 - Generated.soko1_2Potential.boulder 189 + bonus 189 (change p 189 (some 163)))) = true :=
  check_of_implication _ _ (bound520 p)
theorem guard521 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 241 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound521 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 241 .south = true) : bonus 215 p ≤ bonus 241 p := by
  have certified := compare897 p (guard521 p guard)
  simpa only [at215, at241, Int.zero_add] using certified
theorem check521 (p : Pattern) : (!walkGuard soko1_2.board support p 215 241 .south || decide (bonus 215 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound521 p)
theorem guard522 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 216 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound522 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 216 .east = true) : bonus 215 p ≤ bonus 216 p := by
  have certified := compare897 p (guard522 p guard)
  simpa only [at215, at216, Int.zero_add] using certified
theorem check522 (p : Pattern) : (!walkGuard soko1_2.board support p 215 216 .east || decide (bonus 215 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound522 p)
theorem guard523 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 214 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound523 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 214 .west = true) : bonus 215 p ≤ bonus 214 p := by
  have certified := compare897 p (guard523 p guard)
  simpa only [at215, at214, Int.zero_add] using certified
theorem check523 (p : Pattern) : (!walkGuard soko1_2.board support p 215 214 .west || decide (bonus 215 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound523 p)
theorem guard524 (p : Pattern) (guard : pushGuard support p 215 214 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound524 (p : Pattern) (guard : pushGuard support p 215 214 213 213 = true) : bonus 215 p ≤ 1 + Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.boulder 214 + bonus 214 (change p 214 (some 213)) := by
  have certified := compare897 p (guard524 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 214 (some 213))
  have normalized := agree258 _ _ (change_representative support p 214 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check524 (p : Pattern) : (!pushGuard support p 215 214 213 213 || decide (bonus 215 p ≤ 1 + Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.boulder 214 + bonus 214 (change p 214 (some 213)))) = true :=
  check_of_implication _ _ (bound524 p)
theorem guard525 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 190 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound525 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 190 .northEast = true) : bonus 215 p ≤ bonus 190 p := by
  have certified := compare897 p (guard525 p guard)
  simpa only [at215, at190, Int.zero_add] using certified
theorem check525 (p : Pattern) : (!walkGuard soko1_2.board support p 215 190 .northEast || decide (bonus 215 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound525 p)
theorem guard526 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 242 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound526 (p : Pattern) (guard : walkGuard soko1_2.board support p 215 242 .southEast = true) : bonus 215 p ≤ bonus 242 p := by
  have certified := compare897 p (guard526 p guard)
  simpa only [at215, at242, Int.zero_add] using certified
theorem check526 (p : Pattern) : (!walkGuard soko1_2.board support p 215 242 .southEast || decide (bonus 215 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound526 p)
theorem guard527 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 190 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound527 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 190 .north = true) : bonus 216 p ≤ bonus 190 p := by
  have certified := compare897 p (guard527 p guard)
  simpa only [at216, at190, Int.zero_add] using certified
theorem check527 (p : Pattern) : (!walkGuard soko1_2.board support p 216 190 .north || decide (bonus 216 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound527 p)
end NetHack.Sokoban12CostPartition
