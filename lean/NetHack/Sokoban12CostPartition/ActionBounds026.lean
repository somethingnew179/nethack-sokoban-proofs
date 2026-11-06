import NetHack.Sokoban12CostPartition.ActionBounds025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard624 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 271 .south = true) : d1233 p = 1 := by
  change (!false && !(p 271) && !false) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound624 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 271 .south = true) : bonus 245 p ≤ bonus 271 p := by
  have certified := compare6080 p (guard624 p guard)
  simpa only [at245, at271, Int.zero_add] using certified
theorem check624 (p : Pattern) : (!walkGuard soko1_2.board support p 245 271 .south || decide (bonus 245 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound624 p)
theorem guard625 (p : Pattern) (guard : pushGuard support p 245 271 297 297 = true) : d8 p = 1 := by
  change (!false && (!true || (p 271)) && !false && (!false || false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d8, h271] at guard ⊢
theorem bound625 (p : Pattern) (guard : pushGuard support p 245 271 297 297 = true) : bonus 245 p ≤ 1 + Generated.soko1_2Potential.boulder 297 - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some 297)) := by
  have certified := compare6196 p (guard625 p guard)
  change d258 p ≤ (1 : Int) + d733 (change p 271 (some 297))
  have normalized := agree733 _ _ (change_representative support p 271 (some 297) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d733 (change p 271 none)
  rw [sub2702]
  exact certified
theorem check625 (p : Pattern) : (!pushGuard support p 245 271 297 297 || decide (bonus 245 p ≤ 1 + Generated.soko1_2Potential.boulder 297 - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some 297)))) = true :=
  check_of_implication _ _ (bound625 p)
theorem guard626 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 246 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound626 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 246 .east = true) : bonus 245 p ≤ bonus 246 p := by
  have certified := compare897 p (guard626 p guard)
  simpa only [at245, at246, Int.zero_add] using certified
theorem check626 (p : Pattern) : (!walkGuard soko1_2.board support p 245 246 .east || decide (bonus 245 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound626 p)
theorem guard627 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 244 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound627 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 244 .west = true) : bonus 245 p ≤ bonus 244 p := by
  have certified := compare897 p (guard627 p guard)
  simpa only [at245, at244, Int.zero_add] using certified
theorem check627 (p : Pattern) : (!walkGuard soko1_2.board support p 245 244 .west || decide (bonus 245 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound627 p)
theorem guard628 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 220 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound628 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 220 .northEast = true) : bonus 245 p ≤ bonus 220 p := by
  have certified := compare897 p (guard628 p guard)
  simpa only [at245, at220, Int.zero_add] using certified
theorem check628 (p : Pattern) : (!walkGuard soko1_2.board support p 245 220 .northEast || decide (bonus 245 p ≤ bonus 220 p)) = true :=
  check_of_implication _ _ (bound628 p)
theorem guard629 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 218 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound629 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 218 .northWest = true) : bonus 245 p ≤ bonus 218 p := by
  have certified := compare897 p (guard629 p guard)
  simpa only [at245, at218, Int.zero_add] using certified
theorem check629 (p : Pattern) : (!walkGuard soko1_2.board support p 245 218 .northWest || decide (bonus 245 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound629 p)
theorem guard630 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 272 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 271) && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d1, h271] at guard ⊢
theorem bound630 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 272 .southEast = true) : bonus 245 p ≤ bonus 272 p := by
  have certified := compare897 p (guard630 p guard)
  simpa only [at245, at272, Int.zero_add] using certified
theorem check630 (p : Pattern) : (!walkGuard soko1_2.board support p 245 272 .southEast || decide (bonus 245 p ≤ bonus 272 p)) = true :=
  check_of_implication _ _ (bound630 p)
theorem guard631 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 270 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 271) && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d1, h271] at guard ⊢
theorem bound631 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 270 .southWest = true) : bonus 245 p ≤ bonus 270 p := by
  have certified := compare897 p (guard631 p guard)
  simpa only [at245, at270, Int.zero_add] using certified
theorem check631 (p : Pattern) : (!walkGuard soko1_2.board support p 245 270 .southWest || decide (bonus 245 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound631 p)
theorem guard632 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 220 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound632 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 220 .north = true) : bonus 246 p ≤ bonus 220 p := by
  have certified := compare897 p (guard632 p guard)
  simpa only [at246, at220, Int.zero_add] using certified
theorem check632 (p : Pattern) : (!walkGuard soko1_2.board support p 246 220 .north || decide (bonus 246 p ≤ bonus 220 p)) = true :=
  check_of_implication _ _ (bound632 p)
theorem guard633 (p : Pattern) (guard : pushGuard support p 246 220 194 194 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound633 (p : Pattern) (guard : pushGuard support p 246 220 194 194 = true) : bonus 246 p ≤ 1 + Generated.soko1_2Potential.boulder 194 - Generated.soko1_2Potential.boulder 220 + bonus 220 (change p 220 (some 194)) := by
  have certified := compare5431 p (guard633 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 220 (some 194))
  have normalized := agree258 _ _ (change_representative support p 220 (some 194) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check633 (p : Pattern) : (!pushGuard support p 246 220 194 194 || decide (bonus 246 p ≤ 1 + Generated.soko1_2Potential.boulder 194 - Generated.soko1_2Potential.boulder 220 + bonus 220 (change p 220 (some 194)))) = true :=
  check_of_implication _ _ (bound633 p)
theorem guard634 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 272 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound634 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 272 .south = true) : bonus 246 p ≤ bonus 272 p := by
  have certified := compare897 p (guard634 p guard)
  simpa only [at246, at272, Int.zero_add] using certified
theorem check634 (p : Pattern) : (!walkGuard soko1_2.board support p 246 272 .south || decide (bonus 246 p ≤ bonus 272 p)) = true :=
  check_of_implication _ _ (bound634 p)
theorem guard635 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 245 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound635 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 245 .west = true) : bonus 246 p ≤ bonus 245 p := by
  have certified := compare897 p (guard635 p guard)
  simpa only [at246, at245, Int.zero_add] using certified
theorem check635 (p : Pattern) : (!walkGuard soko1_2.board support p 246 245 .west || decide (bonus 246 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound635 p)
theorem guard636 (p : Pattern) (guard : pushGuard support p 246 245 244 244 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound636 (p : Pattern) (guard : pushGuard support p 246 245 244 244 = true) : bonus 246 p ≤ 1 + Generated.soko1_2Potential.boulder 244 - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some 244)) := by
  have certified := compare897 p (guard636 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 245 (some 244))
  have normalized := agree258 _ _ (change_representative support p 245 (some 244) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check636 (p : Pattern) : (!pushGuard support p 246 245 244 244 || decide (bonus 246 p ≤ 1 + Generated.soko1_2Potential.boulder 244 - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some 244)))) = true :=
  check_of_implication _ _ (bound636 p)
theorem guard637 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 219 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound637 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 219 .northWest = true) : bonus 246 p ≤ bonus 219 p := by
  have certified := compare897 p (guard637 p guard)
  simpa only [at246, at219, Int.zero_add] using certified
theorem check637 (p : Pattern) : (!walkGuard soko1_2.board support p 246 219 .northWest || decide (bonus 246 p ≤ bonus 219 p)) = true :=
  check_of_implication _ _ (bound637 p)
theorem guard638 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 271 .southWest = true) : d1233 p = 1 := by
  change (!false && !(p 271) && !(true && false && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound638 (p : Pattern) (guard : walkGuard soko1_2.board support p 246 271 .southWest = true) : bonus 246 p ≤ bonus 271 p := by
  have certified := compare6080 p (guard638 p guard)
  simpa only [at246, at271, Int.zero_add] using certified
theorem check638 (p : Pattern) : (!walkGuard soko1_2.board support p 246 271 .southWest || decide (bonus 246 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound638 p)
theorem guard639 (p : Pattern) (guard : walkGuard soko1_2.board support p 252 278 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound639 (p : Pattern) (guard : walkGuard soko1_2.board support p 252 278 .south = true) : bonus 252 p ≤ bonus 278 p := by
  have certified := compare898 p (guard639 p guard)
  simpa only [at252, at278, Int.zero_add] using certified
theorem check639 (p : Pattern) : (!walkGuard soko1_2.board support p 252 278 .south || decide (bonus 252 p ≤ bonus 278 p)) = true :=
  check_of_implication _ _ (bound639 p)
theorem guard640 (p : Pattern) (guard : pushGuard support p 252 278 304 304 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound640 (p : Pattern) (guard : pushGuard support p 252 278 304 304 = true) : bonus 252 p ≤ 1 + Generated.soko1_2Potential.boulder 304 - Generated.soko1_2Potential.boulder 278 + bonus 278 (change p 278 (some 304)) := by
  have certified := compare1005 p (guard640 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 278 (some 304))
  have normalized := agree0 _ _ (change_representative support p 278 (some 304) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check640 (p : Pattern) : (!pushGuard support p 252 278 304 304 || decide (bonus 252 p ≤ 1 + Generated.soko1_2Potential.boulder 304 - Generated.soko1_2Potential.boulder 278 + bonus 278 (change p 278 (some 304)))) = true :=
  check_of_implication _ _ (bound640 p)
theorem guard641 (p : Pattern) (guard : walkGuard soko1_2.board support p 252 253 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound641 (p : Pattern) (guard : walkGuard soko1_2.board support p 252 253 .east = true) : bonus 252 p ≤ bonus 253 p := by
  have certified := compare898 p (guard641 p guard)
  simpa only [at252, at253, Int.zero_add] using certified
theorem check641 (p : Pattern) : (!walkGuard soko1_2.board support p 252 253 .east || decide (bonus 252 p ≤ bonus 253 p)) = true :=
  check_of_implication _ _ (bound641 p)
theorem guard642 (p : Pattern) (guard : pushGuard support p 252 253 254 254 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound642 (p : Pattern) (guard : pushGuard support p 252 253 254 254 = true) : bonus 252 p ≤ 1 + Generated.soko1_2Potential.boulder 254 - Generated.soko1_2Potential.boulder 253 + bonus 253 (change p 253 (some 254)) := by
  have certified := compare1005 p (guard642 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 253 (some 254))
  have normalized := agree0 _ _ (change_representative support p 253 (some 254) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check642 (p : Pattern) : (!pushGuard support p 252 253 254 254 || decide (bonus 252 p ≤ 1 + Generated.soko1_2Potential.boulder 254 - Generated.soko1_2Potential.boulder 253 + bonus 253 (change p 253 (some 254)))) = true :=
  check_of_implication _ _ (bound642 p)
theorem guard643 (p : Pattern) (guard : walkGuard soko1_2.board support p 252 279 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound643 (p : Pattern) (guard : walkGuard soko1_2.board support p 252 279 .southEast = true) : bonus 252 p ≤ bonus 279 p := by
  have certified := compare898 p (guard643 p guard)
  simpa only [at252, at279, Int.zero_add] using certified
theorem check643 (p : Pattern) : (!walkGuard soko1_2.board support p 252 279 .southEast || decide (bonus 252 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound643 p)
theorem guard644 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 279 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound644 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 279 .south = true) : bonus 253 p ≤ bonus 279 p := by
  have certified := compare898 p (guard644 p guard)
  simpa only [at253, at279, Int.zero_add] using certified
theorem check644 (p : Pattern) : (!walkGuard soko1_2.board support p 253 279 .south || decide (bonus 253 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound644 p)
theorem guard645 (p : Pattern) (guard : pushGuard support p 253 279 305 305 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound645 (p : Pattern) (guard : pushGuard support p 253 279 305 305 = true) : bonus 253 p ≤ 1 + Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some 305)) := by
  have certified := compare1005 p (guard645 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 279 (some 305))
  have normalized := agree0 _ _ (change_representative support p 279 (some 305) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check645 (p : Pattern) : (!pushGuard support p 253 279 305 305 || decide (bonus 253 p ≤ 1 + Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some 305)))) = true :=
  check_of_implication _ _ (bound645 p)
theorem guard646 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 254 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound646 (p : Pattern) (guard : walkGuard soko1_2.board support p 253 254 .east = true) : bonus 253 p ≤ bonus 254 p := by
  have certified := compare898 p (guard646 p guard)
  simpa only [at253, at254, Int.zero_add] using certified
theorem check646 (p : Pattern) : (!walkGuard soko1_2.board support p 253 254 .east || decide (bonus 253 p ≤ bonus 254 p)) = true :=
  check_of_implication _ _ (bound646 p)
theorem guard647 (p : Pattern) (guard : pushGuard support p 253 254 255 255 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound647 (p : Pattern) (guard : pushGuard support p 253 254 255 255 = true) : bonus 253 p ≤ 1 + Generated.soko1_2Potential.boulder 255 - Generated.soko1_2Potential.boulder 254 + bonus 254 (change p 254 (some 255)) := by
  have certified := compare1005 p (guard647 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 254 (some 255))
  have normalized := agree0 _ _ (change_representative support p 254 (some 255) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check647 (p : Pattern) : (!pushGuard support p 253 254 255 255 || decide (bonus 253 p ≤ 1 + Generated.soko1_2Potential.boulder 255 - Generated.soko1_2Potential.boulder 254 + bonus 254 (change p 254 (some 255)))) = true :=
  check_of_implication _ _ (bound647 p)
end NetHack.Sokoban12CostPartition
