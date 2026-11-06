import NetHack.Sokoban12CostPartition.ActionBounds039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard960 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 359 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound960 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 359 .south = true) : bonus 333 p ≤ bonus 359 p := by
  have certified := compare898 p (guard960 p guard)
  simpa only [at333, at359, Int.zero_add] using certified
theorem check960 (p : Pattern) : (!walkGuard soko1_2.board support p 333 359 .south || decide (bonus 333 p ≤ bonus 359 p)) = true :=
  check_of_implication _ _ (bound960 p)
theorem guard961 (p : Pattern) (guard : pushGuard support p 333 359 385 385 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound961 (p : Pattern) (guard : pushGuard support p 333 359 385 385 = true) : bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder 385 - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some 385)) := by
  have certified := compare1005 p (guard961 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 359 (some 385))
  have normalized := agree0 _ _ (change_representative support p 359 (some 385) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check961 (p : Pattern) : (!pushGuard support p 333 359 385 385 || decide (bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder 385 - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some 385)))) = true :=
  check_of_implication _ _ (bound961 p)
theorem guard962 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 334 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound962 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 334 .east = true) : bonus 333 p ≤ bonus 334 p := by
  have certified := compare898 p (guard962 p guard)
  simpa only [at333, at334, Int.zero_add] using certified
theorem check962 (p : Pattern) : (!walkGuard soko1_2.board support p 333 334 .east || decide (bonus 333 p ≤ bonus 334 p)) = true :=
  check_of_implication _ _ (bound962 p)
theorem guard963 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 332 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound963 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 332 .west = true) : bonus 333 p ≤ bonus 332 p := by
  have certified := compare898 p (guard963 p guard)
  simpa only [at333, at332, Int.zero_add] using certified
theorem check963 (p : Pattern) : (!walkGuard soko1_2.board support p 333 332 .west || decide (bonus 333 p ≤ bonus 332 p)) = true :=
  check_of_implication _ _ (bound963 p)
theorem guard964 (p : Pattern) (guard : pushGuard support p 333 332 331 331 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound964 (p : Pattern) (guard : pushGuard support p 333 332 331 331 = true) : bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some 331)) := by
  have certified := compare1005 p (guard964 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 332 (some 331))
  have normalized := agree0 _ _ (change_representative support p 332 (some 331) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check964 (p : Pattern) : (!pushGuard support p 333 332 331 331 || decide (bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some 331)))) = true :=
  check_of_implication _ _ (bound964 p)
theorem guard965 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 308 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound965 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 308 .northEast = true) : bonus 333 p ≤ bonus 308 p := by
  have certified := compare898 p (guard965 p guard)
  simpa only [at333, at308, Int.zero_add] using certified
theorem check965 (p : Pattern) : (!walkGuard soko1_2.board support p 333 308 .northEast || decide (bonus 333 p ≤ bonus 308 p)) = true :=
  check_of_implication _ _ (bound965 p)
theorem guard966 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 306 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound966 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 306 .northWest = true) : bonus 333 p ≤ bonus 306 p := by
  have certified := compare898 p (guard966 p guard)
  simpa only [at333, at306, Int.zero_add] using certified
theorem check966 (p : Pattern) : (!walkGuard soko1_2.board support p 333 306 .northWest || decide (bonus 333 p ≤ bonus 306 p)) = true :=
  check_of_implication _ _ (bound966 p)
theorem guard967 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 360 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound967 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 360 .southEast = true) : bonus 333 p ≤ bonus 360 p := by
  have certified := compare898 p (guard967 p guard)
  simpa only [at333, at360, Int.zero_add] using certified
theorem check967 (p : Pattern) : (!walkGuard soko1_2.board support p 333 360 .southEast || decide (bonus 333 p ≤ bonus 360 p)) = true :=
  check_of_implication _ _ (bound967 p)
theorem guard968 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 358 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound968 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 358 .southWest = true) : bonus 333 p ≤ bonus 358 p := by
  have certified := compare898 p (guard968 p guard)
  simpa only [at333, at358, Int.zero_add] using certified
theorem check968 (p : Pattern) : (!walkGuard soko1_2.board support p 333 358 .southWest || decide (bonus 333 p ≤ bonus 358 p)) = true :=
  check_of_implication _ _ (bound968 p)
theorem guard969 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 308 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound969 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 308 .north = true) : bonus 334 p ≤ bonus 308 p := by
  have certified := compare898 p (guard969 p guard)
  simpa only [at334, at308, Int.zero_add] using certified
theorem check969 (p : Pattern) : (!walkGuard soko1_2.board support p 334 308 .north || decide (bonus 334 p ≤ bonus 308 p)) = true :=
  check_of_implication _ _ (bound969 p)
theorem guard970 (p : Pattern) (guard : pushGuard support p 334 308 282 282 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound970 (p : Pattern) (guard : pushGuard support p 334 308 282 282 = true) : bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder 282 - Generated.soko1_2Potential.boulder 308 + bonus 308 (change p 308 (some 282)) := by
  have certified := compare1005 p (guard970 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 308 (some 282))
  have normalized := agree0 _ _ (change_representative support p 308 (some 282) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check970 (p : Pattern) : (!pushGuard support p 334 308 282 282 || decide (bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder 282 - Generated.soko1_2Potential.boulder 308 + bonus 308 (change p 308 (some 282)))) = true :=
  check_of_implication _ _ (bound970 p)
theorem guard971 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 360 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound971 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 360 .south = true) : bonus 334 p ≤ bonus 360 p := by
  have certified := compare898 p (guard971 p guard)
  simpa only [at334, at360, Int.zero_add] using certified
theorem check971 (p : Pattern) : (!walkGuard soko1_2.board support p 334 360 .south || decide (bonus 334 p ≤ bonus 360 p)) = true :=
  check_of_implication _ _ (bound971 p)
theorem guard972 (p : Pattern) (guard : pushGuard support p 334 360 386 386 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound972 (p : Pattern) (guard : pushGuard support p 334 360 386 386 = true) : bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder 386 - Generated.soko1_2Potential.boulder 360 + bonus 360 (change p 360 (some 386)) := by
  have certified := compare1005 p (guard972 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 360 (some 386))
  have normalized := agree0 _ _ (change_representative support p 360 (some 386) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check972 (p : Pattern) : (!pushGuard support p 334 360 386 386 || decide (bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder 386 - Generated.soko1_2Potential.boulder 360 + bonus 360 (change p 360 (some 386)))) = true :=
  check_of_implication _ _ (bound972 p)
theorem guard973 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 333 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound973 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 333 .west = true) : bonus 334 p ≤ bonus 333 p := by
  have certified := compare898 p (guard973 p guard)
  simpa only [at334, at333, Int.zero_add] using certified
theorem check973 (p : Pattern) : (!walkGuard soko1_2.board support p 334 333 .west || decide (bonus 334 p ≤ bonus 333 p)) = true :=
  check_of_implication _ _ (bound973 p)
theorem guard974 (p : Pattern) (guard : pushGuard support p 334 333 332 332 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound974 (p : Pattern) (guard : pushGuard support p 334 333 332 332 = true) : bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some 332)) := by
  have certified := compare1005 p (guard974 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 333 (some 332))
  have normalized := agree0 _ _ (change_representative support p 333 (some 332) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check974 (p : Pattern) : (!pushGuard support p 334 333 332 332 || decide (bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some 332)))) = true :=
  check_of_implication _ _ (bound974 p)
theorem guard975 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 307 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound975 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 307 .northWest = true) : bonus 334 p ≤ bonus 307 p := by
  have certified := compare898 p (guard975 p guard)
  simpa only [at334, at307, Int.zero_add] using certified
theorem check975 (p : Pattern) : (!walkGuard soko1_2.board support p 334 307 .northWest || decide (bonus 334 p ≤ bonus 307 p)) = true :=
  check_of_implication _ _ (bound975 p)
theorem guard976 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 359 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound976 (p : Pattern) (guard : walkGuard soko1_2.board support p 334 359 .southWest = true) : bonus 334 p ≤ bonus 359 p := by
  have certified := compare898 p (guard976 p guard)
  simpa only [at334, at359, Int.zero_add] using certified
theorem check976 (p : Pattern) : (!walkGuard soko1_2.board support p 334 359 .southWest || decide (bonus 334 p ≤ bonus 359 p)) = true :=
  check_of_implication _ _ (bound976 p)
theorem guard977 (p : Pattern) (guard : walkGuard soko1_2.board support p 336 310 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound977 (p : Pattern) (guard : walkGuard soko1_2.board support p 336 310 .north = true) : bonus 336 p ≤ bonus 310 p := by
  have certified := compare0 p (guard977 p guard)
  simpa only [at336, at310, Int.zero_add] using certified
theorem check977 (p : Pattern) : (!walkGuard soko1_2.board support p 336 310 .north || decide (bonus 336 p ≤ bonus 310 p)) = true :=
  check_of_implication _ _ (bound977 p)
theorem guard978 (p : Pattern) (guard : pushGuard support p 336 310 284 284 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound978 (p : Pattern) (guard : pushGuard support p 336 310 284 284 = true) : bonus 336 p ≤ 1 + Generated.soko1_2Potential.boulder 284 - Generated.soko1_2Potential.boulder 310 + bonus 310 (change p 310 (some 284)) := by
  have certified := compare3 p (guard978 p guard)
  change d75 p ≤ (1 : Int) + d75 (change p 310 (some 284))
  have normalized := agree75 _ _ (change_representative support p 310 (some 284) 10000 dummy_outside)
  rw [normalized]
  change d75 p ≤ (1 : Int) + d75 (change p 10000 none)
  rw [sub34]
  exact certified
theorem check978 (p : Pattern) : (!pushGuard support p 336 310 284 284 || decide (bonus 336 p ≤ 1 + Generated.soko1_2Potential.boulder 284 - Generated.soko1_2Potential.boulder 310 + bonus 310 (change p 310 (some 284)))) = true :=
  check_of_implication _ _ (bound978 p)
theorem guard979 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 319 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound979 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 319 .north = true) : bonus 345 p ≤ bonus 319 p := by
  have certified := compare897 p (guard979 p guard)
  simpa only [at345, at319, Int.zero_add] using certified
theorem check979 (p : Pattern) : (!walkGuard soko1_2.board support p 345 319 .north || decide (bonus 345 p ≤ bonus 319 p)) = true :=
  check_of_implication _ _ (bound979 p)
theorem guard980 (p : Pattern) (guard : pushGuard support p 345 319 293 293 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound980 (p : Pattern) (guard : pushGuard support p 345 319 293 293 = true) : bonus 345 p ≤ 1 + Generated.soko1_2Potential.boulder 293 - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some 293)) := by
  have certified := compare897 p (guard980 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 319 (some 293))
  have normalized := agree258 _ _ (change_representative support p 319 (some 293) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check980 (p : Pattern) : (!pushGuard support p 345 319 293 293 || decide (bonus 345 p ≤ 1 + Generated.soko1_2Potential.boulder 293 - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some 293)))) = true :=
  check_of_implication _ _ (bound980 p)
theorem guard981 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 371 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound981 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 371 .south = true) : bonus 345 p ≤ bonus 371 p := by
  have certified := compare897 p (guard981 p guard)
  simpa only [at345, at371, Int.zero_add] using certified
theorem check981 (p : Pattern) : (!walkGuard soko1_2.board support p 345 371 .south || decide (bonus 345 p ≤ bonus 371 p)) = true :=
  check_of_implication _ _ (bound981 p)
theorem guard982 (p : Pattern) (guard : pushGuard support p 345 371 397 397 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound982 (p : Pattern) (guard : pushGuard support p 345 371 397 397 = true) : bonus 345 p ≤ 1 + Generated.soko1_2Potential.boulder 397 - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some 397)) := by
  have certified := compare2570 p (guard982 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 371 (some 397))
  have normalized := agree258 _ _ (change_representative support p 371 (some 397) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check982 (p : Pattern) : (!pushGuard support p 345 371 397 397 || decide (bonus 345 p ≤ 1 + Generated.soko1_2Potential.boulder 397 - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some 397)))) = true :=
  check_of_implication _ _ (bound982 p)
theorem guard983 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 320 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound983 (p : Pattern) (guard : walkGuard soko1_2.board support p 345 320 .northEast = true) : bonus 345 p ≤ bonus 320 p := by
  have certified := compare897 p (guard983 p guard)
  simpa only [at345, at320, Int.zero_add] using certified
theorem check983 (p : Pattern) : (!walkGuard soko1_2.board support p 345 320 .northEast || decide (bonus 345 p ≤ bonus 320 p)) = true :=
  check_of_implication _ _ (bound983 p)
end NetHack.Sokoban12CostPartition
