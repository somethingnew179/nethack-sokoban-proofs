import NetHack.Sokoban12CostPartition.ActionBounds029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard720 (p : Pattern) (guard : pushGuard support p 271 245 219 219 = true) : d1233 p = 1 := by
  change (!(p 271) && (!false || false) && !false && (!false || false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound720 (p : Pattern) (guard : pushGuard support p 271 245 219 219 = true) : bonus 271 p ≤ 1 + Generated.soko1_2Potential.boulder 219 - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some 219)) := by
  have certified := compare6290 p (guard720 p guard)
  change d733 p ≤ (0 : Int) + d258 (change p 245 (some 219))
  have normalized := agree258 _ _ (change_representative support p 245 (some 219) 10000 dummy_outside)
  rw [normalized]
  change d733 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check720 (p : Pattern) : (!pushGuard support p 271 245 219 219 || decide (bonus 271 p ≤ 1 + Generated.soko1_2Potential.boulder 219 - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some 219)))) = true :=
  check_of_implication _ _ (bound720 p)
theorem guard721 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 297 .south = true) : d1233 p = 1 := by
  change (!(p 271) && !false && !false) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound721 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 297 .south = true) : bonus 271 p ≤ bonus 297 p := by
  have certified := compare6290 p (guard721 p guard)
  simpa only [at271, at297, Int.zero_add] using certified
theorem check721 (p : Pattern) : (!walkGuard soko1_2.board support p 271 297 .south || decide (bonus 271 p ≤ bonus 297 p)) = true :=
  check_of_implication _ _ (bound721 p)
theorem guard722 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 272 .east = true) : d1233 p = 1 := by
  change (!(p 271) && !false && !false) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound722 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 272 .east = true) : bonus 271 p ≤ bonus 272 p := by
  have certified := compare6290 p (guard722 p guard)
  simpa only [at271, at272, Int.zero_add] using certified
theorem check722 (p : Pattern) : (!walkGuard soko1_2.board support p 271 272 .east || decide (bonus 271 p ≤ bonus 272 p)) = true :=
  check_of_implication _ _ (bound722 p)
theorem guard723 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 270 .west = true) : d1233 p = 1 := by
  change (!(p 271) && !false && !false) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound723 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 270 .west = true) : bonus 271 p ≤ bonus 270 p := by
  have certified := compare6290 p (guard723 p guard)
  simpa only [at271, at270, Int.zero_add] using certified
theorem check723 (p : Pattern) : (!walkGuard soko1_2.board support p 271 270 .west || decide (bonus 271 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound723 p)
theorem guard724 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 246 .northEast = true) : d1233 p = 1 := by
  change (!(p 271) && !false && !(true && false && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound724 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 246 .northEast = true) : bonus 271 p ≤ bonus 246 p := by
  have certified := compare6290 p (guard724 p guard)
  simpa only [at271, at246, Int.zero_add] using certified
theorem check724 (p : Pattern) : (!walkGuard soko1_2.board support p 271 246 .northEast || decide (bonus 271 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound724 p)
theorem guard725 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 244 .northWest = true) : d1233 p = 1 := by
  change (!(p 271) && !false && !(true && false && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound725 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 244 .northWest = true) : bonus 271 p ≤ bonus 244 p := by
  have certified := compare6290 p (guard725 p guard)
  simpa only [at271, at244, Int.zero_add] using certified
theorem check725 (p : Pattern) : (!walkGuard soko1_2.board support p 271 244 .northWest || decide (bonus 271 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound725 p)
theorem guard726 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 296 .southWest = true) : d1233 p = 1 := by
  change (!(p 271) && !false && !(true && false && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound726 (p : Pattern) (guard : walkGuard soko1_2.board support p 271 296 .southWest = true) : bonus 271 p ≤ bonus 296 p := by
  have certified := compare6290 p (guard726 p guard)
  simpa only [at271, at296, Int.zero_add] using certified
theorem check726 (p : Pattern) : (!walkGuard soko1_2.board support p 271 296 .southWest || decide (bonus 271 p ≤ bonus 296 p)) = true :=
  check_of_implication _ _ (bound726 p)
theorem guard727 (p : Pattern) (guard : walkGuard soko1_2.board support p 272 246 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound727 (p : Pattern) (guard : walkGuard soko1_2.board support p 272 246 .north = true) : bonus 272 p ≤ bonus 246 p := by
  have certified := compare897 p (guard727 p guard)
  simpa only [at272, at246, Int.zero_add] using certified
theorem check727 (p : Pattern) : (!walkGuard soko1_2.board support p 272 246 .north || decide (bonus 272 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound727 p)
theorem guard728 (p : Pattern) (guard : pushGuard support p 272 246 220 220 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound728 (p : Pattern) (guard : pushGuard support p 272 246 220 220 = true) : bonus 272 p ≤ 1 + Generated.soko1_2Potential.boulder 220 - Generated.soko1_2Potential.boulder 246 + bonus 246 (change p 246 (some 220)) := by
  have certified := compare5431 p (guard728 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 246 (some 220))
  have normalized := agree258 _ _ (change_representative support p 246 (some 220) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check728 (p : Pattern) : (!pushGuard support p 272 246 220 220 || decide (bonus 272 p ≤ 1 + Generated.soko1_2Potential.boulder 220 - Generated.soko1_2Potential.boulder 246 + bonus 246 (change p 246 (some 220)))) = true :=
  check_of_implication _ _ (bound728 p)
theorem guard729 (p : Pattern) (guard : walkGuard soko1_2.board support p 272 271 .west = true) : d1233 p = 1 := by
  change (!false && !(p 271) && !false) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound729 (p : Pattern) (guard : walkGuard soko1_2.board support p 272 271 .west = true) : bonus 272 p ≤ bonus 271 p := by
  have certified := compare6080 p (guard729 p guard)
  simpa only [at272, at271, Int.zero_add] using certified
theorem check729 (p : Pattern) : (!walkGuard soko1_2.board support p 272 271 .west || decide (bonus 272 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound729 p)
theorem guard730 (p : Pattern) (guard : pushGuard support p 272 271 270 270 = true) : d8 p = 1 := by
  change (!false && (!true || (p 271)) && !false && (!false || false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d8, h271] at guard ⊢
theorem bound730 (p : Pattern) (guard : pushGuard support p 272 271 270 270 = true) : bonus 272 p ≤ 1 + Generated.soko1_2Potential.boulder 270 - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some 270)) := by
  have certified := compare6196 p (guard730 p guard)
  change d258 p ≤ (1 : Int) + d733 (change p 271 (some 270))
  have normalized := agree733 _ _ (change_representative support p 271 (some 270) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d733 (change p 271 none)
  rw [sub2702]
  exact certified
theorem check730 (p : Pattern) : (!pushGuard support p 272 271 270 270 || decide (bonus 272 p ≤ 1 + Generated.soko1_2Potential.boulder 270 - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some 270)))) = true :=
  check_of_implication _ _ (bound730 p)
theorem guard731 (p : Pattern) (guard : walkGuard soko1_2.board support p 272 245 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 271))) = true at guard
  cases h271 : p 271
  all_goals simp [d1, h271] at guard ⊢
theorem bound731 (p : Pattern) (guard : walkGuard soko1_2.board support p 272 245 .northWest = true) : bonus 272 p ≤ bonus 245 p := by
  have certified := compare897 p (guard731 p guard)
  simpa only [at272, at245, Int.zero_add] using certified
theorem check731 (p : Pattern) : (!walkGuard soko1_2.board support p 272 245 .northWest || decide (bonus 272 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound731 p)
theorem guard732 (p : Pattern) (guard : walkGuard soko1_2.board support p 272 297 .southWest = true) : d1233 p = 1 := by
  change (!false && !false && !(true && true && (p 271))) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound732 (p : Pattern) (guard : walkGuard soko1_2.board support p 272 297 .southWest = true) : bonus 272 p ≤ bonus 297 p := by
  have certified := compare6291 p (guard732 p guard)
  simpa only [at272, at297, Int.zero_add] using certified
theorem check732 (p : Pattern) : (!walkGuard soko1_2.board support p 272 297 .southWest || decide (bonus 272 p ≤ bonus 297 p)) = true :=
  check_of_implication _ _ (bound732 p)
theorem guard733 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 252 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound733 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 252 .north = true) : bonus 278 p ≤ bonus 252 p := by
  have certified := compare898 p (guard733 p guard)
  simpa only [at278, at252, Int.zero_add] using certified
theorem check733 (p : Pattern) : (!walkGuard soko1_2.board support p 278 252 .north || decide (bonus 278 p ≤ bonus 252 p)) = true :=
  check_of_implication _ _ (bound733 p)
theorem guard734 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 304 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound734 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 304 .south = true) : bonus 278 p ≤ bonus 304 p := by
  have certified := compare898 p (guard734 p guard)
  simpa only [at278, at304, Int.zero_add] using certified
theorem check734 (p : Pattern) : (!walkGuard soko1_2.board support p 278 304 .south || decide (bonus 278 p ≤ bonus 304 p)) = true :=
  check_of_implication _ _ (bound734 p)
theorem guard735 (p : Pattern) (guard : pushGuard support p 278 304 330 330 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound735 (p : Pattern) (guard : pushGuard support p 278 304 330 330 = true) : bonus 278 p ≤ 1 + Generated.soko1_2Potential.boulder 330 - Generated.soko1_2Potential.boulder 304 + bonus 304 (change p 304 (some 330)) := by
  have certified := compare1005 p (guard735 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 304 (some 330))
  have normalized := agree0 _ _ (change_representative support p 304 (some 330) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check735 (p : Pattern) : (!pushGuard support p 278 304 330 330 || decide (bonus 278 p ≤ 1 + Generated.soko1_2Potential.boulder 330 - Generated.soko1_2Potential.boulder 304 + bonus 304 (change p 304 (some 330)))) = true :=
  check_of_implication _ _ (bound735 p)
theorem guard736 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 279 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound736 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 279 .east = true) : bonus 278 p ≤ bonus 279 p := by
  have certified := compare898 p (guard736 p guard)
  simpa only [at278, at279, Int.zero_add] using certified
theorem check736 (p : Pattern) : (!walkGuard soko1_2.board support p 278 279 .east || decide (bonus 278 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound736 p)
theorem guard737 (p : Pattern) (guard : pushGuard support p 278 279 280 280 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound737 (p : Pattern) (guard : pushGuard support p 278 279 280 280 = true) : bonus 278 p ≤ 1 + Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some 280)) := by
  have certified := compare1005 p (guard737 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 279 (some 280))
  have normalized := agree0 _ _ (change_representative support p 279 (some 280) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check737 (p : Pattern) : (!pushGuard support p 278 279 280 280 || decide (bonus 278 p ≤ 1 + Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some 280)))) = true :=
  check_of_implication _ _ (bound737 p)
theorem guard738 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 253 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound738 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 253 .northEast = true) : bonus 278 p ≤ bonus 253 p := by
  have certified := compare898 p (guard738 p guard)
  simpa only [at278, at253, Int.zero_add] using certified
theorem check738 (p : Pattern) : (!walkGuard soko1_2.board support p 278 253 .northEast || decide (bonus 278 p ≤ bonus 253 p)) = true :=
  check_of_implication _ _ (bound738 p)
theorem guard739 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 305 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound739 (p : Pattern) (guard : walkGuard soko1_2.board support p 278 305 .southEast = true) : bonus 278 p ≤ bonus 305 p := by
  have certified := compare898 p (guard739 p guard)
  simpa only [at278, at305, Int.zero_add] using certified
theorem check739 (p : Pattern) : (!walkGuard soko1_2.board support p 278 305 .southEast || decide (bonus 278 p ≤ bonus 305 p)) = true :=
  check_of_implication _ _ (bound739 p)
theorem guard740 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 253 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound740 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 253 .north = true) : bonus 279 p ≤ bonus 253 p := by
  have certified := compare898 p (guard740 p guard)
  simpa only [at279, at253, Int.zero_add] using certified
theorem check740 (p : Pattern) : (!walkGuard soko1_2.board support p 279 253 .north || decide (bonus 279 p ≤ bonus 253 p)) = true :=
  check_of_implication _ _ (bound740 p)
theorem guard741 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 305 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound741 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 305 .south = true) : bonus 279 p ≤ bonus 305 p := by
  have certified := compare898 p (guard741 p guard)
  simpa only [at279, at305, Int.zero_add] using certified
theorem check741 (p : Pattern) : (!walkGuard soko1_2.board support p 279 305 .south || decide (bonus 279 p ≤ bonus 305 p)) = true :=
  check_of_implication _ _ (bound741 p)
theorem guard742 (p : Pattern) (guard : pushGuard support p 279 305 331 331 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound742 (p : Pattern) (guard : pushGuard support p 279 305 331 331 = true) : bonus 279 p ≤ 1 + Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some 331)) := by
  have certified := compare1005 p (guard742 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 305 (some 331))
  have normalized := agree0 _ _ (change_representative support p 305 (some 331) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check742 (p : Pattern) : (!pushGuard support p 279 305 331 331 || decide (bonus 279 p ≤ 1 + Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some 331)))) = true :=
  check_of_implication _ _ (bound742 p)
theorem guard743 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 280 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound743 (p : Pattern) (guard : walkGuard soko1_2.board support p 279 280 .east = true) : bonus 279 p ≤ bonus 280 p := by
  have certified := compare898 p (guard743 p guard)
  simpa only [at279, at280, Int.zero_add] using certified
theorem check743 (p : Pattern) : (!walkGuard soko1_2.board support p 279 280 .east || decide (bonus 279 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound743 p)
end NetHack.Sokoban12CostPartition
