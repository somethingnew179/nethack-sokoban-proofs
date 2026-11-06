import NetHack.Sokoban12CostPartition.ActionBounds036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard888 (p : Pattern) (guard : pushGuard support p 308 334 360 360 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound888 (p : Pattern) (guard : pushGuard support p 308 334 360 360 = true) : bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder 360 - Generated.soko1_2Potential.boulder 334 + bonus 334 (change p 334 (some 360)) := by
  have certified := compare1005 p (guard888 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 334 (some 360))
  have normalized := agree0 _ _ (change_representative support p 334 (some 360) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check888 (p : Pattern) : (!pushGuard support p 308 334 360 360 || decide (bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder 360 - Generated.soko1_2Potential.boulder 334 + bonus 334 (change p 334 (some 360)))) = true :=
  check_of_implication _ _ (bound888 p)
theorem guard889 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 307 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound889 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 307 .west = true) : bonus 308 p ≤ bonus 307 p := by
  have certified := compare898 p (guard889 p guard)
  simpa only [at308, at307, Int.zero_add] using certified
theorem check889 (p : Pattern) : (!walkGuard soko1_2.board support p 308 307 .west || decide (bonus 308 p ≤ bonus 307 p)) = true :=
  check_of_implication _ _ (bound889 p)
theorem guard890 (p : Pattern) (guard : pushGuard support p 308 307 306 306 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound890 (p : Pattern) (guard : pushGuard support p 308 307 306 306 = true) : bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some 306)) := by
  have certified := compare1005 p (guard890 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 307 (some 306))
  have normalized := agree0 _ _ (change_representative support p 307 (some 306) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check890 (p : Pattern) : (!pushGuard support p 308 307 306 306 || decide (bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some 306)))) = true :=
  check_of_implication _ _ (bound890 p)
theorem guard891 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 281 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound891 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 281 .northWest = true) : bonus 308 p ≤ bonus 281 p := by
  have certified := compare898 p (guard891 p guard)
  simpa only [at308, at281, Int.zero_add] using certified
theorem check891 (p : Pattern) : (!walkGuard soko1_2.board support p 308 281 .northWest || decide (bonus 308 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound891 p)
theorem guard892 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 333 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound892 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 333 .southWest = true) : bonus 308 p ≤ bonus 333 p := by
  have certified := compare898 p (guard892 p guard)
  simpa only [at308, at333, Int.zero_add] using certified
theorem check892 (p : Pattern) : (!walkGuard soko1_2.board support p 308 333 .southWest || decide (bonus 308 p ≤ bonus 333 p)) = true :=
  check_of_implication _ _ (bound892 p)
theorem guard893 (p : Pattern) (guard : walkGuard soko1_2.board support p 310 284 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound893 (p : Pattern) (guard : walkGuard soko1_2.board support p 310 284 .north = true) : bonus 310 p ≤ bonus 284 p := by
  have certified := compare0 p (guard893 p guard)
  simpa only [at310, at284, Int.zero_add] using certified
theorem check893 (p : Pattern) : (!walkGuard soko1_2.board support p 310 284 .north || decide (bonus 310 p ≤ bonus 284 p)) = true :=
  check_of_implication _ _ (bound893 p)
theorem guard894 (p : Pattern) (guard : pushGuard support p 310 284 258 258 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound894 (p : Pattern) (guard : pushGuard support p 310 284 258 258 = true) : bonus 310 p ≤ 1 + Generated.soko1_2Potential.boulder 258 - Generated.soko1_2Potential.boulder 284 + bonus 284 (change p 284 (some 258)) := by
  have certified := compare3 p (guard894 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 284 (some 258))
  have normalized := agree75 _ _ (change_representative support p 284 (some 258) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check894 (p : Pattern) : (!pushGuard support p 310 284 258 258 || decide (bonus 310 p ≤ 1 + Generated.soko1_2Potential.boulder 258 - Generated.soko1_2Potential.boulder 284 + bonus 284 (change p 284 (some 258)))) = true :=
  check_of_implication _ _ (bound894 p)
theorem guard895 (p : Pattern) (guard : walkGuard soko1_2.board support p 310 336 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound895 (p : Pattern) (guard : walkGuard soko1_2.board support p 310 336 .south = true) : bonus 310 p ≤ bonus 336 p := by
  have certified := compare0 p (guard895 p guard)
  simpa only [at310, at336, Int.zero_add] using certified
theorem check895 (p : Pattern) : (!walkGuard soko1_2.board support p 310 336 .south || decide (bonus 310 p ≤ bonus 336 p)) = true :=
  check_of_implication _ _ (bound895 p)
theorem guard896 (p : Pattern) (guard : walkGuard soko1_2.board support p 317 291 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound896 (p : Pattern) (guard : walkGuard soko1_2.board support p 317 291 .north = true) : bonus 317 p ≤ bonus 291 p := by
  have certified := compare897 p (guard896 p guard)
  simpa only [at317, at291, Int.zero_add] using certified
theorem check896 (p : Pattern) : (!walkGuard soko1_2.board support p 317 291 .north || decide (bonus 317 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound896 p)
theorem guard897 (p : Pattern) (guard : pushGuard support p 317 291 265 265 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound897 (p : Pattern) (guard : pushGuard support p 317 291 265 265 = true) : bonus 317 p ≤ 1 + Generated.soko1_2Potential.boulder 265 - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some 265)) := by
  have certified := compare897 p (guard897 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 291 (some 265))
  have normalized := agree258 _ _ (change_representative support p 291 (some 265) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check897 (p : Pattern) : (!pushGuard support p 317 291 265 265 || decide (bonus 317 p ≤ 1 + Generated.soko1_2Potential.boulder 265 - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some 265)))) = true :=
  check_of_implication _ _ (bound897 p)
theorem guard898 (p : Pattern) (guard : walkGuard soko1_2.board support p 317 318 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound898 (p : Pattern) (guard : walkGuard soko1_2.board support p 317 318 .east = true) : bonus 317 p ≤ bonus 318 p := by
  have certified := compare897 p (guard898 p guard)
  simpa only [at317, at318, Int.zero_add] using certified
theorem check898 (p : Pattern) : (!walkGuard soko1_2.board support p 317 318 .east || decide (bonus 317 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound898 p)
theorem guard899 (p : Pattern) (guard : pushGuard support p 317 318 319 319 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound899 (p : Pattern) (guard : pushGuard support p 317 318 319 319 = true) : bonus 317 p ≤ 1 + Generated.soko1_2Potential.boulder 319 - Generated.soko1_2Potential.boulder 318 + bonus 318 (change p 318 (some 319)) := by
  have certified := compare897 p (guard899 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 318 (some 319))
  have normalized := agree258 _ _ (change_representative support p 318 (some 319) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check899 (p : Pattern) : (!pushGuard support p 317 318 319 319 || decide (bonus 317 p ≤ 1 + Generated.soko1_2Potential.boulder 319 - Generated.soko1_2Potential.boulder 318 + bonus 318 (change p 318 (some 319)))) = true :=
  check_of_implication _ _ (bound899 p)
theorem guard900 (p : Pattern) (guard : walkGuard soko1_2.board support p 317 292 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound900 (p : Pattern) (guard : walkGuard soko1_2.board support p 317 292 .northEast = true) : bonus 317 p ≤ bonus 292 p := by
  have certified := compare897 p (guard900 p guard)
  simpa only [at317, at292, Int.zero_add] using certified
theorem check900 (p : Pattern) : (!walkGuard soko1_2.board support p 317 292 .northEast || decide (bonus 317 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound900 p)
theorem guard901 (p : Pattern) (guard : walkGuard soko1_2.board support p 317 290 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound901 (p : Pattern) (guard : walkGuard soko1_2.board support p 317 290 .northWest = true) : bonus 317 p ≤ bonus 290 p := by
  have certified := compare897 p (guard901 p guard)
  simpa only [at317, at290, Int.zero_add] using certified
theorem check901 (p : Pattern) : (!walkGuard soko1_2.board support p 317 290 .northWest || decide (bonus 317 p ≤ bonus 290 p)) = true :=
  check_of_implication _ _ (bound901 p)
theorem guard902 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 292 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound902 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 292 .north = true) : bonus 318 p ≤ bonus 292 p := by
  have certified := compare897 p (guard902 p guard)
  simpa only [at318, at292, Int.zero_add] using certified
theorem check902 (p : Pattern) : (!walkGuard soko1_2.board support p 318 292 .north || decide (bonus 318 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound902 p)
theorem guard903 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 319 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound903 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 319 .east = true) : bonus 318 p ≤ bonus 319 p := by
  have certified := compare897 p (guard903 p guard)
  simpa only [at318, at319, Int.zero_add] using certified
theorem check903 (p : Pattern) : (!walkGuard soko1_2.board support p 318 319 .east || decide (bonus 318 p ≤ bonus 319 p)) = true :=
  check_of_implication _ _ (bound903 p)
theorem guard904 (p : Pattern) (guard : pushGuard support p 318 319 320 320 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound904 (p : Pattern) (guard : pushGuard support p 318 319 320 320 = true) : bonus 318 p ≤ 1 + Generated.soko1_2Potential.boulder 320 - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some 320)) := by
  have certified := compare5790 p (guard904 p guard)
  change d258 p ≤ (4 : Int) + d258 (change p 319 (some 320))
  have normalized := agree258 _ _ (change_representative support p 319 (some 320) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (4 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check904 (p : Pattern) : (!pushGuard support p 318 319 320 320 || decide (bonus 318 p ≤ 1 + Generated.soko1_2Potential.boulder 320 - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some 320)))) = true :=
  check_of_implication _ _ (bound904 p)
theorem guard905 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 317 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound905 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 317 .west = true) : bonus 318 p ≤ bonus 317 p := by
  have certified := compare897 p (guard905 p guard)
  simpa only [at318, at317, Int.zero_add] using certified
theorem check905 (p : Pattern) : (!walkGuard soko1_2.board support p 318 317 .west || decide (bonus 318 p ≤ bonus 317 p)) = true :=
  check_of_implication _ _ (bound905 p)
theorem guard906 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 293 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound906 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 293 .northEast = true) : bonus 318 p ≤ bonus 293 p := by
  have certified := compare897 p (guard906 p guard)
  simpa only [at318, at293, Int.zero_add] using certified
theorem check906 (p : Pattern) : (!walkGuard soko1_2.board support p 318 293 .northEast || decide (bonus 318 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound906 p)
theorem guard907 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 291 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound907 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 291 .northWest = true) : bonus 318 p ≤ bonus 291 p := by
  have certified := compare897 p (guard907 p guard)
  simpa only [at318, at291, Int.zero_add] using certified
theorem check907 (p : Pattern) : (!walkGuard soko1_2.board support p 318 291 .northWest || decide (bonus 318 p ≤ bonus 291 p)) = true :=
  check_of_implication _ _ (bound907 p)
theorem guard908 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 345 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound908 (p : Pattern) (guard : walkGuard soko1_2.board support p 318 345 .southEast = true) : bonus 318 p ≤ bonus 345 p := by
  have certified := compare897 p (guard908 p guard)
  simpa only [at318, at345, Int.zero_add] using certified
theorem check908 (p : Pattern) : (!walkGuard soko1_2.board support p 318 345 .southEast || decide (bonus 318 p ≤ bonus 345 p)) = true :=
  check_of_implication _ _ (bound908 p)
theorem guard909 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 293 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound909 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 293 .north = true) : bonus 319 p ≤ bonus 293 p := by
  have certified := compare897 p (guard909 p guard)
  simpa only [at319, at293, Int.zero_add] using certified
theorem check909 (p : Pattern) : (!walkGuard soko1_2.board support p 319 293 .north || decide (bonus 319 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound909 p)
theorem guard910 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 345 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound910 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 345 .south = true) : bonus 319 p ≤ bonus 345 p := by
  have certified := compare897 p (guard910 p guard)
  simpa only [at319, at345, Int.zero_add] using certified
theorem check910 (p : Pattern) : (!walkGuard soko1_2.board support p 319 345 .south || decide (bonus 319 p ≤ bonus 345 p)) = true :=
  check_of_implication _ _ (bound910 p)
theorem guard911 (p : Pattern) (guard : pushGuard support p 319 345 371 371 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound911 (p : Pattern) (guard : pushGuard support p 319 345 371 371 = true) : bonus 319 p ≤ 1 + Generated.soko1_2Potential.boulder 371 - Generated.soko1_2Potential.boulder 345 + bonus 345 (change p 345 (some 371)) := by
  have certified := compare2570 p (guard911 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 345 (some 371))
  have normalized := agree258 _ _ (change_representative support p 345 (some 371) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check911 (p : Pattern) : (!pushGuard support p 319 345 371 371 || decide (bonus 319 p ≤ 1 + Generated.soko1_2Potential.boulder 371 - Generated.soko1_2Potential.boulder 345 + bonus 345 (change p 345 (some 371)))) = true :=
  check_of_implication _ _ (bound911 p)
end NetHack.Sokoban12CostPartition
