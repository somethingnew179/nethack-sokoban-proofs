import NetHack.Sokoban12CostPartition.ActionBounds031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard768 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 254 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound768 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 254 .northWest = true) : bonus 281 p ≤ bonus 254 p := by
  have certified := compare898 p (guard768 p guard)
  simpa only [at281, at254, Int.zero_add] using certified
theorem check768 (p : Pattern) : (!walkGuard soko1_2.board support p 281 254 .northWest || decide (bonus 281 p ≤ bonus 254 p)) = true :=
  check_of_implication _ _ (bound768 p)
theorem guard769 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 308 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound769 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 308 .southEast = true) : bonus 281 p ≤ bonus 308 p := by
  have certified := compare898 p (guard769 p guard)
  simpa only [at281, at308, Int.zero_add] using certified
theorem check769 (p : Pattern) : (!walkGuard soko1_2.board support p 281 308 .southEast || decide (bonus 281 p ≤ bonus 308 p)) = true :=
  check_of_implication _ _ (bound769 p)
theorem guard770 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 306 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound770 (p : Pattern) (guard : walkGuard soko1_2.board support p 281 306 .southWest = true) : bonus 281 p ≤ bonus 306 p := by
  have certified := compare898 p (guard770 p guard)
  simpa only [at281, at306, Int.zero_add] using certified
theorem check770 (p : Pattern) : (!walkGuard soko1_2.board support p 281 306 .southWest || decide (bonus 281 p ≤ bonus 306 p)) = true :=
  check_of_implication _ _ (bound770 p)
theorem guard771 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 256 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound771 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 256 .north = true) : bonus 282 p ≤ bonus 256 p := by
  have certified := compare898 p (guard771 p guard)
  simpa only [at282, at256, Int.zero_add] using certified
theorem check771 (p : Pattern) : (!walkGuard soko1_2.board support p 282 256 .north || decide (bonus 282 p ≤ bonus 256 p)) = true :=
  check_of_implication _ _ (bound771 p)
theorem guard772 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 308 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound772 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 308 .south = true) : bonus 282 p ≤ bonus 308 p := by
  have certified := compare898 p (guard772 p guard)
  simpa only [at282, at308, Int.zero_add] using certified
theorem check772 (p : Pattern) : (!walkGuard soko1_2.board support p 282 308 .south || decide (bonus 282 p ≤ bonus 308 p)) = true :=
  check_of_implication _ _ (bound772 p)
theorem guard773 (p : Pattern) (guard : pushGuard support p 282 308 334 334 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound773 (p : Pattern) (guard : pushGuard support p 282 308 334 334 = true) : bonus 282 p ≤ 1 + Generated.soko1_2Potential.boulder 334 - Generated.soko1_2Potential.boulder 308 + bonus 308 (change p 308 (some 334)) := by
  have certified := compare1005 p (guard773 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 308 (some 334))
  have normalized := agree0 _ _ (change_representative support p 308 (some 334) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check773 (p : Pattern) : (!pushGuard support p 282 308 334 334 || decide (bonus 282 p ≤ 1 + Generated.soko1_2Potential.boulder 334 - Generated.soko1_2Potential.boulder 308 + bonus 308 (change p 308 (some 334)))) = true :=
  check_of_implication _ _ (bound773 p)
theorem guard774 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 281 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound774 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 281 .west = true) : bonus 282 p ≤ bonus 281 p := by
  have certified := compare898 p (guard774 p guard)
  simpa only [at282, at281, Int.zero_add] using certified
theorem check774 (p : Pattern) : (!walkGuard soko1_2.board support p 282 281 .west || decide (bonus 282 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound774 p)
theorem guard775 (p : Pattern) (guard : pushGuard support p 282 281 280 280 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound775 (p : Pattern) (guard : pushGuard support p 282 281 280 280 = true) : bonus 282 p ≤ 1 + Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some 280)) := by
  have certified := compare1005 p (guard775 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 281 (some 280))
  have normalized := agree0 _ _ (change_representative support p 281 (some 280) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check775 (p : Pattern) : (!pushGuard support p 282 281 280 280 || decide (bonus 282 p ≤ 1 + Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some 280)))) = true :=
  check_of_implication _ _ (bound775 p)
theorem guard776 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 255 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound776 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 255 .northWest = true) : bonus 282 p ≤ bonus 255 p := by
  have certified := compare898 p (guard776 p guard)
  simpa only [at282, at255, Int.zero_add] using certified
theorem check776 (p : Pattern) : (!walkGuard soko1_2.board support p 282 255 .northWest || decide (bonus 282 p ≤ bonus 255 p)) = true :=
  check_of_implication _ _ (bound776 p)
theorem guard777 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 307 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound777 (p : Pattern) (guard : walkGuard soko1_2.board support p 282 307 .southWest = true) : bonus 282 p ≤ bonus 307 p := by
  have certified := compare898 p (guard777 p guard)
  simpa only [at282, at307, Int.zero_add] using certified
theorem check777 (p : Pattern) : (!walkGuard soko1_2.board support p 282 307 .southWest || decide (bonus 282 p ≤ bonus 307 p)) = true :=
  check_of_implication _ _ (bound777 p)
theorem guard778 (p : Pattern) (guard : walkGuard soko1_2.board support p 284 258 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound778 (p : Pattern) (guard : walkGuard soko1_2.board support p 284 258 .north = true) : bonus 284 p ≤ bonus 258 p := by
  have certified := compare0 p (guard778 p guard)
  simpa only [at284, at258, Int.zero_add] using certified
theorem check778 (p : Pattern) : (!walkGuard soko1_2.board support p 284 258 .north || decide (bonus 284 p ≤ bonus 258 p)) = true :=
  check_of_implication _ _ (bound778 p)
theorem guard779 (p : Pattern) (guard : pushGuard support p 284 258 232 232 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound779 (p : Pattern) (guard : pushGuard support p 284 258 232 232 = true) : bonus 284 p ≤ 1 + Generated.soko1_2Potential.boulder 232 - Generated.soko1_2Potential.boulder 258 + bonus 258 (change p 258 (some 232)) := by
  have certified := compare3 p (guard779 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 258 (some 232))
  have normalized := agree75 _ _ (change_representative support p 258 (some 232) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check779 (p : Pattern) : (!pushGuard support p 284 258 232 232 || decide (bonus 284 p ≤ 1 + Generated.soko1_2Potential.boulder 232 - Generated.soko1_2Potential.boulder 258 + bonus 258 (change p 258 (some 232)))) = true :=
  check_of_implication _ _ (bound779 p)
theorem guard780 (p : Pattern) (guard : walkGuard soko1_2.board support p 284 310 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound780 (p : Pattern) (guard : walkGuard soko1_2.board support p 284 310 .south = true) : bonus 284 p ≤ bonus 310 p := by
  have certified := compare0 p (guard780 p guard)
  simpa only [at284, at310, Int.zero_add] using certified
theorem check780 (p : Pattern) : (!walkGuard soko1_2.board support p 284 310 .south || decide (bonus 284 p ≤ bonus 310 p)) = true :=
  check_of_implication _ _ (bound780 p)
theorem guard781 (p : Pattern) (guard : pushGuard support p 284 310 336 336 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound781 (p : Pattern) (guard : pushGuard support p 284 310 336 336 = true) : bonus 284 p ≤ 1 + Generated.soko1_2Potential.boulder 336 - Generated.soko1_2Potential.boulder 310 + bonus 310 (change p 310 (some 336)) := by
  have certified := compare3 p (guard781 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 310 (some 336))
  have normalized := agree75 _ _ (change_representative support p 310 (some 336) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check781 (p : Pattern) : (!pushGuard support p 284 310 336 336 || decide (bonus 284 p ≤ 1 + Generated.soko1_2Potential.boulder 336 - Generated.soko1_2Potential.boulder 310 + bonus 310 (change p 310 (some 336)))) = true :=
  check_of_implication _ _ (bound781 p)
theorem guard782 (p : Pattern) (guard : walkGuard soko1_2.board support p 288 262 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound782 (p : Pattern) (guard : walkGuard soko1_2.board support p 288 262 .north = true) : bonus 288 p ≤ bonus 262 p := by
  have certified := compare897 p (guard782 p guard)
  simpa only [at288, at262, Int.zero_add] using certified
theorem check782 (p : Pattern) : (!walkGuard soko1_2.board support p 288 262 .north || decide (bonus 288 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound782 p)
theorem guard783 (p : Pattern) (guard : pushGuard support p 288 262 236 236 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound783 (p : Pattern) (guard : pushGuard support p 288 262 236 236 = true) : bonus 288 p ≤ 1 + Generated.soko1_2Potential.boulder 236 - Generated.soko1_2Potential.boulder 262 + bonus 262 (change p 262 (some 236)) := by
  have certified := compare897 p (guard783 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 262 (some 236))
  have normalized := agree258 _ _ (change_representative support p 262 (some 236) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check783 (p : Pattern) : (!pushGuard support p 288 262 236 236 || decide (bonus 288 p ≤ 1 + Generated.soko1_2Potential.boulder 236 - Generated.soko1_2Potential.boulder 262 + bonus 262 (change p 262 (some 236)))) = true :=
  check_of_implication _ _ (bound783 p)
theorem guard784 (p : Pattern) (guard : walkGuard soko1_2.board support p 288 289 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound784 (p : Pattern) (guard : walkGuard soko1_2.board support p 288 289 .east = true) : bonus 288 p ≤ bonus 289 p := by
  have certified := compare897 p (guard784 p guard)
  simpa only [at288, at289, Int.zero_add] using certified
theorem check784 (p : Pattern) : (!walkGuard soko1_2.board support p 288 289 .east || decide (bonus 288 p ≤ bonus 289 p)) = true :=
  check_of_implication _ _ (bound784 p)
theorem guard785 (p : Pattern) (guard : pushGuard support p 288 289 290 290 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound785 (p : Pattern) (guard : pushGuard support p 288 289 290 290 = true) : bonus 288 p ≤ 1 + Generated.soko1_2Potential.boulder 290 - Generated.soko1_2Potential.boulder 289 + bonus 289 (change p 289 (some 290)) := by
  have certified := compare897 p (guard785 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 289 (some 290))
  have normalized := agree258 _ _ (change_representative support p 289 (some 290) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check785 (p : Pattern) : (!pushGuard support p 288 289 290 290 || decide (bonus 288 p ≤ 1 + Generated.soko1_2Potential.boulder 290 - Generated.soko1_2Potential.boulder 289 + bonus 289 (change p 289 (some 290)))) = true :=
  check_of_implication _ _ (bound785 p)
theorem guard786 (p : Pattern) (guard : walkGuard soko1_2.board support p 288 263 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound786 (p : Pattern) (guard : walkGuard soko1_2.board support p 288 263 .northEast = true) : bonus 288 p ≤ bonus 263 p := by
  have certified := compare897 p (guard786 p guard)
  simpa only [at288, at263, Int.zero_add] using certified
theorem check786 (p : Pattern) : (!walkGuard soko1_2.board support p 288 263 .northEast || decide (bonus 288 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound786 p)
theorem guard787 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 263 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound787 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 263 .north = true) : bonus 289 p ≤ bonus 263 p := by
  have certified := compare897 p (guard787 p guard)
  simpa only [at289, at263, Int.zero_add] using certified
theorem check787 (p : Pattern) : (!walkGuard soko1_2.board support p 289 263 .north || decide (bonus 289 p ≤ bonus 263 p)) = true :=
  check_of_implication _ _ (bound787 p)
theorem guard788 (p : Pattern) (guard : pushGuard support p 289 263 237 237 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound788 (p : Pattern) (guard : pushGuard support p 289 263 237 237 = true) : bonus 289 p ≤ 1 + Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some 237)) := by
  have certified := compare897 p (guard788 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 263 (some 237))
  have normalized := agree258 _ _ (change_representative support p 263 (some 237) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check788 (p : Pattern) : (!pushGuard support p 289 263 237 237 || decide (bonus 289 p ≤ 1 + Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some 237)))) = true :=
  check_of_implication _ _ (bound788 p)
theorem guard789 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 290 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound789 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 290 .east = true) : bonus 289 p ≤ bonus 290 p := by
  have certified := compare897 p (guard789 p guard)
  simpa only [at289, at290, Int.zero_add] using certified
theorem check789 (p : Pattern) : (!walkGuard soko1_2.board support p 289 290 .east || decide (bonus 289 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound789 p)
theorem guard790 (p : Pattern) (guard : pushGuard support p 289 290 291 291 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound790 (p : Pattern) (guard : pushGuard support p 289 290 291 291 = true) : bonus 289 p ≤ 1 + Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.boulder 290 + bonus 290 (change p 290 (some 291)) := by
  have certified := compare897 p (guard790 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 290 (some 291))
  have normalized := agree258 _ _ (change_representative support p 290 (some 291) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check790 (p : Pattern) : (!pushGuard support p 289 290 291 291 || decide (bonus 289 p ≤ 1 + Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.boulder 290 + bonus 290 (change p 290 (some 291)))) = true :=
  check_of_implication _ _ (bound790 p)
theorem guard791 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 288 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound791 (p : Pattern) (guard : walkGuard soko1_2.board support p 289 288 .west = true) : bonus 289 p ≤ bonus 288 p := by
  have certified := compare897 p (guard791 p guard)
  simpa only [at289, at288, Int.zero_add] using certified
theorem check791 (p : Pattern) : (!walkGuard soko1_2.board support p 289 288 .west || decide (bonus 289 p ≤ bonus 288 p)) = true :=
  check_of_implication _ _ (bound791 p)
end NetHack.Sokoban12CostPartition
