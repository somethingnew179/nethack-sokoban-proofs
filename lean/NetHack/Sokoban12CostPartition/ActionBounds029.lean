import NetHack.Sokoban12CostPartition.ActionBounds028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard696 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 263 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound696 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 263 .west = true) : bonus 264 p ≤ bonus 263 p := by
  have certified := compare897 p (guard696 p guard)
  simpa only [at264, at263, Int.zero_add] using certified
theorem check696 (p : Pattern) : (!walkGuard soko1_2.board support p 264 263 .west || decide (bonus 264 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound696 p)
theorem guard697 (p : Pattern) (guard : pushGuard support p 264 263 262 262 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound697 (p : Pattern) (guard : pushGuard support p 264 263 262 262 = true) : bonus 264 p ≤ 1 + Generated.soko1_2Potential.boulder 262 - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some 262)) := by
  have certified := compare2570 p (guard697 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 263 (some 262))
  have normalized := agree258 _ _ (change_representative support p 263 (some 262) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check697 (p : Pattern) : (!pushGuard support p 264 263 262 262 || decide (bonus 264 p ≤ 1 + Generated.soko1_2Potential.boulder 262 - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some 262)))) = true :=
  check_of_implication _ _ (bound697 p)
theorem guard698 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 239 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound698 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 239 .northEast = true) : bonus 264 p ≤ bonus 239 p := by
  have certified := compare897 p (guard698 p guard)
  simpa only [at264, at239, Int.zero_add] using certified
theorem check698 (p : Pattern) : (!walkGuard soko1_2.board support p 264 239 .northEast || decide (bonus 264 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound698 p)
theorem guard699 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 237 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound699 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 237 .northWest = true) : bonus 264 p ≤ bonus 237 p := by
  have certified := compare897 p (guard699 p guard)
  simpa only [at264, at237, Int.zero_add] using certified
theorem check699 (p : Pattern) : (!walkGuard soko1_2.board support p 264 237 .northWest || decide (bonus 264 p ≤ bonus 237 p)) = true :=
  check_of_implication _ _ (bound699 p)
theorem guard700 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 291 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound700 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 291 .southEast = true) : bonus 264 p ≤ bonus 291 p := by
  have certified := compare897 p (guard700 p guard)
  simpa only [at264, at291, Int.zero_add] using certified
theorem check700 (p : Pattern) : (!walkGuard soko1_2.board support p 264 291 .southEast || decide (bonus 264 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound700 p)
theorem guard701 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 289 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound701 (p : Pattern) (guard : walkGuard soko1_2.board support p 264 289 .southWest = true) : bonus 264 p ≤ bonus 289 p := by
  have certified := compare897 p (guard701 p guard)
  simpa only [at264, at289, Int.zero_add] using certified
theorem check701 (p : Pattern) : (!walkGuard soko1_2.board support p 264 289 .southWest || decide (bonus 264 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound701 p)
theorem guard702 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 239 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound702 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 239 .north = true) : bonus 265 p ≤ bonus 239 p := by
  have certified := compare897 p (guard702 p guard)
  simpa only [at265, at239, Int.zero_add] using certified
theorem check702 (p : Pattern) : (!walkGuard soko1_2.board support p 265 239 .north || decide (bonus 265 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound702 p)
theorem guard703 (p : Pattern) (guard : pushGuard support p 265 239 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound703 (p : Pattern) (guard : pushGuard support p 265 239 213 213 = true) : bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.boulder 239 + bonus 239 (change p 239 (some 213)) := by
  have certified := compare897 p (guard703 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 239 (some 213))
  have normalized := agree258 _ _ (change_representative support p 239 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check703 (p : Pattern) : (!pushGuard support p 265 239 213 213 || decide (bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.boulder 239 + bonus 239 (change p 239 (some 213)))) = true :=
  check_of_implication _ _ (bound703 p)
theorem guard704 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 291 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound704 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 291 .south = true) : bonus 265 p ≤ bonus 291 p := by
  have certified := compare897 p (guard704 p guard)
  simpa only [at265, at291, Int.zero_add] using certified
theorem check704 (p : Pattern) : (!walkGuard soko1_2.board support p 265 291 .south || decide (bonus 265 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound704 p)
theorem guard705 (p : Pattern) (guard : pushGuard support p 265 291 317 317 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound705 (p : Pattern) (guard : pushGuard support p 265 291 317 317 = true) : bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder 317 - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some 317)) := by
  have certified := compare5791 p (guard705 p guard)
  change d258 p ≤ (7 : Int) + d258 (change p 291 (some 317))
  have normalized := agree258 _ _ (change_representative support p 291 (some 317) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (7 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check705 (p : Pattern) : (!pushGuard support p 265 291 317 317 || decide (bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder 317 - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some 317)))) = true :=
  check_of_implication _ _ (bound705 p)
theorem guard706 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 264 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound706 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 264 .west = true) : bonus 265 p ≤ bonus 264 p := by
  have certified := compare897 p (guard706 p guard)
  simpa only [at265, at264, Int.zero_add] using certified
theorem check706 (p : Pattern) : (!walkGuard soko1_2.board support p 265 264 .west || decide (bonus 265 p ≤ bonus 264 p)) = true :=
  check_of_implication _ _ (bound706 p)
theorem guard707 (p : Pattern) (guard : pushGuard support p 265 264 263 263 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound707 (p : Pattern) (guard : pushGuard support p 265 264 263 263 = true) : bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder 263 - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some 263)) := by
  have certified := compare2570 p (guard707 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 264 (some 263))
  have normalized := agree258 _ _ (change_representative support p 264 (some 263) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check707 (p : Pattern) : (!pushGuard support p 265 264 263 263 || decide (bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder 263 - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some 263)))) = true :=
  check_of_implication _ _ (bound707 p)
theorem guard708 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 238 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound708 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 238 .northWest = true) : bonus 265 p ≤ bonus 238 p := by
  have certified := compare897 p (guard708 p guard)
  simpa only [at265, at238, Int.zero_add] using certified
theorem check708 (p : Pattern) : (!walkGuard soko1_2.board support p 265 238 .northWest || decide (bonus 265 p ≤ bonus 238 p)) = true :=
  check_of_implication _ _ (bound708 p)
theorem guard709 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 292 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound709 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 292 .southEast = true) : bonus 265 p ≤ bonus 292 p := by
  have certified := compare897 p (guard709 p guard)
  simpa only [at265, at292, Int.zero_add] using certified
theorem check709 (p : Pattern) : (!walkGuard soko1_2.board support p 265 292 .southEast || decide (bonus 265 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound709 p)
theorem guard710 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 290 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound710 (p : Pattern) (guard : walkGuard soko1_2.board support p 265 290 .southWest = true) : bonus 265 p ≤ bonus 290 p := by
  have certified := compare897 p (guard710 p guard)
  simpa only [at265, at290, Int.zero_add] using certified
theorem check710 (p : Pattern) : (!walkGuard soko1_2.board support p 265 290 .southWest || decide (bonus 265 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound710 p)
theorem guard711 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 244 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound711 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 244 .north = true) : bonus 270 p ≤ bonus 244 p := by
  have certified := compare897 p (guard711 p guard)
  simpa only [at270, at244, Int.zero_add] using certified
theorem check711 (p : Pattern) : (!walkGuard soko1_2.board support p 270 244 .north || decide (bonus 270 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound711 p)
theorem guard712 (p : Pattern) (guard : pushGuard support p 270 244 218 218 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound712 (p : Pattern) (guard : pushGuard support p 270 244 218 218 = true) : bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder 218 - Generated.soko1_2Potential.boulder 244 + bonus 244 (change p 244 (some 218)) := by
  have certified := compare897 p (guard712 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 244 (some 218))
  have normalized := agree258 _ _ (change_representative support p 244 (some 218) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check712 (p : Pattern) : (!pushGuard support p 270 244 218 218 || decide (bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder 218 - Generated.soko1_2Potential.boulder 244 + bonus 244 (change p 244 (some 218)))) = true :=
  check_of_implication _ _ (bound712 p)
theorem guard713 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 296 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound713 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 296 .south = true) : bonus 270 p ≤ bonus 296 p := by
  have certified := compare897 p (guard713 p guard)
  simpa only [at270, at296, Int.zero_add] using certified
theorem check713 (p : Pattern) : (!walkGuard soko1_2.board support p 270 296 .south || decide (bonus 270 p ≤ bonus 296 p)) = true :=
  check_of_implication _ _ (bound713 p)
theorem guard714 (p : Pattern) (guard : pushGuard support p 270 296 322 322 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound714 (p : Pattern) (guard : pushGuard support p 270 296 322 322 = true) : bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder 322 - Generated.soko1_2Potential.boulder 296 + bonus 296 (change p 296 (some 322)) := by
  have certified := compare5431 p (guard714 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 296 (some 322))
  have normalized := agree258 _ _ (change_representative support p 296 (some 322) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check714 (p : Pattern) : (!pushGuard support p 270 296 322 322 || decide (bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder 322 - Generated.soko1_2Potential.boulder 296 + bonus 296 (change p 296 (some 322)))) = true :=
  check_of_implication _ _ (bound714 p)
theorem guard715 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 271 .east = true) : d1233 p = 1 := by
  change (!false && !(p 271) && !false) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound715 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 271 .east = true) : bonus 270 p ≤ bonus 271 p := by
  have certified := compare6080 p (guard715 p guard)
  simpa only [at270, at271, Int.zero_add] using certified
theorem check715 (p : Pattern) : (!walkGuard soko1_2.board support p 270 271 .east || decide (bonus 270 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound715 p)
theorem guard716 (p : Pattern) (guard : pushGuard support p 270 271 272 272 = true) : d8 p = 1 := by
  change (!false && (!true || (p 271)) && !false && (!false || false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d8, h271] at guard ⊢
theorem bound716 (p : Pattern) (guard : pushGuard support p 270 271 272 272 = true) : bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder 272 - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some 272)) := by
  have certified := compare6196 p (guard716 p guard)
  change d258 p ≤ (1 : Int) + d733 (change p 271 (some 272))
  have normalized := agree733 _ _ (change_representative support p 271 (some 272) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d733 (change p 271 none)
  rw [sub2702]
  exact certified
theorem check716 (p : Pattern) : (!pushGuard support p 270 271 272 272 || decide (bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder 272 - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some 272)))) = true :=
  check_of_implication _ _ (bound716 p)
theorem guard717 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 245 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 271))) = true at guard
  cases h271 : p 271
  all_goals simp [d1, h271] at guard ⊢
theorem bound717 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 245 .northEast = true) : bonus 270 p ≤ bonus 245 p := by
  have certified := compare897 p (guard717 p guard)
  simpa only [at270, at245, Int.zero_add] using certified
theorem check717 (p : Pattern) : (!walkGuard soko1_2.board support p 270 245 .northEast || decide (bonus 270 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound717 p)
theorem guard718 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 297 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 271))) = true at guard
  cases h271 : p 271
  all_goals simp [d1, h271] at guard ⊢
theorem bound718 (p : Pattern) (guard : walkGuard soko1_2.board support p 270 297 .southEast = true) : bonus 270 p ≤ bonus 297 p := by
  have certified := compare897 p (guard718 p guard)
  simpa only [at270, at297, Int.zero_add] using certified
theorem check718 (p : Pattern) : (!walkGuard soko1_2.board support p 270 297 .southEast || decide (bonus 270 p ≤ bonus 297 p)) = true :=
  check_of_implication _ _ (bound718 p)
theorem guard719 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 245 .north = true) : d1233 p = 1 := by
  change (!(p 271) && !false && !false) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound719 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 245 .north = true) : bonus 271 p ≤ bonus 245 p := by
  have certified := compare6290 p (guard719 p guard)
  simpa only [at271, at245, Int.zero_add] using certified
theorem check719 (p : Pattern) : (!walkGuard soko1_2.board support p 271 245 .north || decide (bonus 271 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound719 p)
end NetHack.Sokoban12CostPartition
