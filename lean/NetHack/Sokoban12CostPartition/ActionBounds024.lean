import NetHack.Sokoban12CostPartition.ActionBounds023
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard576 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 263 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound576 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 263 .south = true) : bonus 237 p ≤ bonus 263 p := by
  have certified := compare897 p (guard576 p guard)
  simpa only [at237, at263, Int.zero_add] using certified
theorem check576 (p : Pattern) : (!walkGuard soko1_2.board support p 237 263 .south || decide (bonus 237 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound576 p)
theorem guard577 (p : Pattern) (guard : pushGuard support p 237 263 289 289 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound577 (p : Pattern) (guard : pushGuard support p 237 263 289 289 = true) : bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder 289 - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some 289)) := by
  have certified := compare5790 p (guard577 p guard)
  change d258 p ≤ (4 : Int) + d258 (change p 263 (some 289))
  have normalized := agree258 _ _ (change_representative support p 263 (some 289) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (4 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check577 (p : Pattern) : (!pushGuard support p 237 263 289 289 || decide (bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder 289 - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some 289)))) = true :=
  check_of_implication _ _ (bound577 p)
theorem guard578 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 238 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound578 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 238 .east = true) : bonus 237 p ≤ bonus 238 p := by
  have certified := compare897 p (guard578 p guard)
  simpa only [at237, at238, Int.zero_add] using certified
theorem check578 (p : Pattern) : (!walkGuard soko1_2.board support p 237 238 .east || decide (bonus 237 p ≤ bonus 238 p)) = true :=
  check_of_implication _ _ (bound578 p)
theorem guard579 (p : Pattern) (guard : pushGuard support p 237 238 239 239 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound579 (p : Pattern) (guard : pushGuard support p 237 238 239 239 = true) : bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder 239 - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some 239)) := by
  have certified := compare2570 p (guard579 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 238 (some 239))
  have normalized := agree258 _ _ (change_representative support p 238 (some 239) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check579 (p : Pattern) : (!pushGuard support p 237 238 239 239 || decide (bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder 239 - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some 239)))) = true :=
  check_of_implication _ _ (bound579 p)
theorem guard580 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 236 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound580 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 236 .west = true) : bonus 237 p ≤ bonus 236 p := by
  have certified := compare897 p (guard580 p guard)
  simpa only [at237, at236, Int.zero_add] using certified
theorem check580 (p : Pattern) : (!walkGuard soko1_2.board support p 237 236 .west || decide (bonus 237 p ≤ bonus 236 p)) = true :=
  check_of_implication _ _ (bound580 p)
theorem guard581 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 212 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound581 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 212 .northEast = true) : bonus 237 p ≤ bonus 212 p := by
  have certified := compare897 p (guard581 p guard)
  simpa only [at237, at212, Int.zero_add] using certified
theorem check581 (p : Pattern) : (!walkGuard soko1_2.board support p 237 212 .northEast || decide (bonus 237 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound581 p)
theorem guard582 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 210 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound582 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 210 .northWest = true) : bonus 237 p ≤ bonus 210 p := by
  have certified := compare897 p (guard582 p guard)
  simpa only [at237, at210, Int.zero_add] using certified
theorem check582 (p : Pattern) : (!walkGuard soko1_2.board support p 237 210 .northWest || decide (bonus 237 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound582 p)
theorem guard583 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 264 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound583 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 264 .southEast = true) : bonus 237 p ≤ bonus 264 p := by
  have certified := compare897 p (guard583 p guard)
  simpa only [at237, at264, Int.zero_add] using certified
theorem check583 (p : Pattern) : (!walkGuard soko1_2.board support p 237 264 .southEast || decide (bonus 237 p ≤ bonus 264 p)) = true :=
  check_of_implication _ _ (bound583 p)
theorem guard584 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 262 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound584 (p : Pattern) (guard : walkGuard soko1_2.board support p 237 262 .southWest = true) : bonus 237 p ≤ bonus 262 p := by
  have certified := compare897 p (guard584 p guard)
  simpa only [at237, at262, Int.zero_add] using certified
theorem check584 (p : Pattern) : (!walkGuard soko1_2.board support p 237 262 .southWest || decide (bonus 237 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound584 p)
theorem guard585 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 212 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound585 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 212 .north = true) : bonus 238 p ≤ bonus 212 p := by
  have certified := compare897 p (guard585 p guard)
  simpa only [at238, at212, Int.zero_add] using certified
theorem check585 (p : Pattern) : (!walkGuard soko1_2.board support p 238 212 .north || decide (bonus 238 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound585 p)
theorem guard586 (p : Pattern) (guard : pushGuard support p 238 212 186 186 = true) : d829 p = 1 := by
  change (!false && (!false || false) && !(p 186) && (!(p 186) || false)) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound586 (p : Pattern) (guard : pushGuard support p 238 212 186 186 = true) : bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some 186)) := by
  have certified := compare3550 p (guard586 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 212 (some 186))
  have normalized := agree258 _ _ (change_representative support p 212 (some 186) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 (some 186))
  rw [sub1901]
  exact certified
theorem check586 (p : Pattern) : (!pushGuard support p 238 212 186 186 || decide (bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some 186)))) = true :=
  check_of_implication _ _ (bound586 p)
theorem guard587 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 264 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound587 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 264 .south = true) : bonus 238 p ≤ bonus 264 p := by
  have certified := compare897 p (guard587 p guard)
  simpa only [at238, at264, Int.zero_add] using certified
theorem check587 (p : Pattern) : (!walkGuard soko1_2.board support p 238 264 .south || decide (bonus 238 p ≤ bonus 264 p)) = true :=
  check_of_implication _ _ (bound587 p)
theorem guard588 (p : Pattern) (guard : pushGuard support p 238 264 290 290 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound588 (p : Pattern) (guard : pushGuard support p 238 264 290 290 = true) : bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder 290 - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some 290)) := by
  have certified := compare5790 p (guard588 p guard)
  change d258 p ≤ (4 : Int) + d258 (change p 264 (some 290))
  have normalized := agree258 _ _ (change_representative support p 264 (some 290) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (4 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check588 (p : Pattern) : (!pushGuard support p 238 264 290 290 || decide (bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder 290 - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some 290)))) = true :=
  check_of_implication _ _ (bound588 p)
theorem guard589 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 239 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound589 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 239 .east = true) : bonus 238 p ≤ bonus 239 p := by
  have certified := compare897 p (guard589 p guard)
  simpa only [at238, at239, Int.zero_add] using certified
theorem check589 (p : Pattern) : (!walkGuard soko1_2.board support p 238 239 .east || decide (bonus 238 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound589 p)
theorem guard590 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 237 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound590 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 237 .west = true) : bonus 238 p ≤ bonus 237 p := by
  have certified := compare897 p (guard590 p guard)
  simpa only [at238, at237, Int.zero_add] using certified
theorem check590 (p : Pattern) : (!walkGuard soko1_2.board support p 238 237 .west || decide (bonus 238 p ≤ bonus 237 p)) = true :=
  check_of_implication _ _ (bound590 p)
theorem guard591 (p : Pattern) (guard : pushGuard support p 238 237 236 236 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound591 (p : Pattern) (guard : pushGuard support p 238 237 236 236 = true) : bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder 236 - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some 236)) := by
  have certified := compare2570 p (guard591 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 237 (some 236))
  have normalized := agree258 _ _ (change_representative support p 237 (some 236) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check591 (p : Pattern) : (!pushGuard support p 238 237 236 236 || decide (bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder 236 - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some 236)))) = true :=
  check_of_implication _ _ (bound591 p)
theorem guard592 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 213 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound592 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 213 .northEast = true) : bonus 238 p ≤ bonus 213 p := by
  have certified := compare897 p (guard592 p guard)
  simpa only [at238, at213, Int.zero_add] using certified
theorem check592 (p : Pattern) : (!walkGuard soko1_2.board support p 238 213 .northEast || decide (bonus 238 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound592 p)
theorem guard593 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 211 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound593 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 211 .northWest = true) : bonus 238 p ≤ bonus 211 p := by
  have certified := compare897 p (guard593 p guard)
  simpa only [at238, at211, Int.zero_add] using certified
theorem check593 (p : Pattern) : (!walkGuard soko1_2.board support p 238 211 .northWest || decide (bonus 238 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound593 p)
theorem guard594 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 265 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound594 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 265 .southEast = true) : bonus 238 p ≤ bonus 265 p := by
  have certified := compare897 p (guard594 p guard)
  simpa only [at238, at265, Int.zero_add] using certified
theorem check594 (p : Pattern) : (!walkGuard soko1_2.board support p 238 265 .southEast || decide (bonus 238 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound594 p)
theorem guard595 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 263 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound595 (p : Pattern) (guard : walkGuard soko1_2.board support p 238 263 .southWest = true) : bonus 238 p ≤ bonus 263 p := by
  have certified := compare897 p (guard595 p guard)
  simpa only [at238, at263, Int.zero_add] using certified
theorem check595 (p : Pattern) : (!walkGuard soko1_2.board support p 238 263 .southWest || decide (bonus 238 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound595 p)
theorem guard596 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 213 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound596 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 213 .north = true) : bonus 239 p ≤ bonus 213 p := by
  have certified := compare897 p (guard596 p guard)
  simpa only [at239, at213, Int.zero_add] using certified
theorem check596 (p : Pattern) : (!walkGuard soko1_2.board support p 239 213 .north || decide (bonus 239 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound596 p)
theorem guard597 (p : Pattern) (guard : pushGuard support p 239 213 187 187 = true) : d851 p = 1 := by
  change (!false && (!false || false) && !(p 187) && (!(p 187) || false)) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound597 (p : Pattern) (guard : pushGuard support p 239 213 187 187 = true) : bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder 187 - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some 187)) := by
  have certified := compare5979 p (guard597 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 213 (some 187))
  have normalized := agree258 _ _ (change_representative support p 213 (some 187) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 (some 187))
  rw [sub2611]
  exact certified
theorem check597 (p : Pattern) : (!pushGuard support p 239 213 187 187 || decide (bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder 187 - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some 187)))) = true :=
  check_of_implication _ _ (bound597 p)
theorem guard598 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 265 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound598 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 265 .south = true) : bonus 239 p ≤ bonus 265 p := by
  have certified := compare897 p (guard598 p guard)
  simpa only [at239, at265, Int.zero_add] using certified
theorem check598 (p : Pattern) : (!walkGuard soko1_2.board support p 239 265 .south || decide (bonus 239 p ≤ bonus 265 p)) = true :=
  check_of_implication _ _ (bound598 p)
theorem guard599 (p : Pattern) (guard : pushGuard support p 239 265 291 291 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound599 (p : Pattern) (guard : pushGuard support p 239 265 291 291 = true) : bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.boulder 265 + bonus 265 (change p 265 (some 291)) := by
  have certified := compare2570 p (guard599 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 265 (some 291))
  have normalized := agree258 _ _ (change_representative support p 265 (some 291) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check599 (p : Pattern) : (!pushGuard support p 239 265 291 291 || decide (bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.boulder 265 + bonus 265 (change p 265 (some 291)))) = true :=
  check_of_implication _ _ (bound599 p)
end NetHack.Sokoban12CostPartition
