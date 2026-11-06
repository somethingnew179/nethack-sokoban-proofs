import NetHack.Sokoban12CostPartition.ActionBounds038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard936 (p : Pattern) (guard : pushGuard support p 331 305 279 279 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound936 (p : Pattern) (guard : pushGuard support p 331 305 279 279 = true) : bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder 279 - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some 279)) := by
  have certified := compare1005 p (guard936 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 305 (some 279))
  have normalized := agree0 _ _ (change_representative support p 305 (some 279) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check936 (p : Pattern) : (!pushGuard support p 331 305 279 279 || decide (bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder 279 - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some 279)))) = true :=
  check_of_implication _ _ (bound936 p)
theorem guard937 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 357 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound937 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 357 .south = true) : bonus 331 p ≤ bonus 357 p := by
  have certified := compare898 p (guard937 p guard)
  simpa only [at331, at357, Int.zero_add] using certified
theorem check937 (p : Pattern) : (!walkGuard soko1_2.board support p 331 357 .south || decide (bonus 331 p ≤ bonus 357 p)) = true :=
  check_of_implication _ _ (bound937 p)
theorem guard938 (p : Pattern) (guard : pushGuard support p 331 357 383 383 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound938 (p : Pattern) (guard : pushGuard support p 331 357 383 383 = true) : bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder 383 - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some 383)) := by
  have certified := compare1005 p (guard938 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 357 (some 383))
  have normalized := agree0 _ _ (change_representative support p 357 (some 383) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check938 (p : Pattern) : (!pushGuard support p 331 357 383 383 || decide (bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder 383 - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some 383)))) = true :=
  check_of_implication _ _ (bound938 p)
theorem guard939 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 332 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound939 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 332 .east = true) : bonus 331 p ≤ bonus 332 p := by
  have certified := compare898 p (guard939 p guard)
  simpa only [at331, at332, Int.zero_add] using certified
theorem check939 (p : Pattern) : (!walkGuard soko1_2.board support p 331 332 .east || decide (bonus 331 p ≤ bonus 332 p)) = true :=
  check_of_implication _ _ (bound939 p)
theorem guard940 (p : Pattern) (guard : pushGuard support p 331 332 333 333 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound940 (p : Pattern) (guard : pushGuard support p 331 332 333 333 = true) : bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some 333)) := by
  have certified := compare1005 p (guard940 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 332 (some 333))
  have normalized := agree0 _ _ (change_representative support p 332 (some 333) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check940 (p : Pattern) : (!pushGuard support p 331 332 333 333 || decide (bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some 333)))) = true :=
  check_of_implication _ _ (bound940 p)
theorem guard941 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 330 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound941 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 330 .west = true) : bonus 331 p ≤ bonus 330 p := by
  have certified := compare898 p (guard941 p guard)
  simpa only [at331, at330, Int.zero_add] using certified
theorem check941 (p : Pattern) : (!walkGuard soko1_2.board support p 331 330 .west || decide (bonus 331 p ≤ bonus 330 p)) = true :=
  check_of_implication _ _ (bound941 p)
theorem guard942 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 306 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound942 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 306 .northEast = true) : bonus 331 p ≤ bonus 306 p := by
  have certified := compare898 p (guard942 p guard)
  simpa only [at331, at306, Int.zero_add] using certified
theorem check942 (p : Pattern) : (!walkGuard soko1_2.board support p 331 306 .northEast || decide (bonus 331 p ≤ bonus 306 p)) = true :=
  check_of_implication _ _ (bound942 p)
theorem guard943 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 304 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound943 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 304 .northWest = true) : bonus 331 p ≤ bonus 304 p := by
  have certified := compare898 p (guard943 p guard)
  simpa only [at331, at304, Int.zero_add] using certified
theorem check943 (p : Pattern) : (!walkGuard soko1_2.board support p 331 304 .northWest || decide (bonus 331 p ≤ bonus 304 p)) = true :=
  check_of_implication _ _ (bound943 p)
theorem guard944 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 358 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound944 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 358 .southEast = true) : bonus 331 p ≤ bonus 358 p := by
  have certified := compare898 p (guard944 p guard)
  simpa only [at331, at358, Int.zero_add] using certified
theorem check944 (p : Pattern) : (!walkGuard soko1_2.board support p 331 358 .southEast || decide (bonus 331 p ≤ bonus 358 p)) = true :=
  check_of_implication _ _ (bound944 p)
theorem guard945 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 356 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound945 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 356 .southWest = true) : bonus 331 p ≤ bonus 356 p := by
  have certified := compare898 p (guard945 p guard)
  simpa only [at331, at356, Int.zero_add] using certified
theorem check945 (p : Pattern) : (!walkGuard soko1_2.board support p 331 356 .southWest || decide (bonus 331 p ≤ bonus 356 p)) = true :=
  check_of_implication _ _ (bound945 p)
theorem guard946 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 306 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound946 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 306 .north = true) : bonus 332 p ≤ bonus 306 p := by
  have certified := compare898 p (guard946 p guard)
  simpa only [at332, at306, Int.zero_add] using certified
theorem check946 (p : Pattern) : (!walkGuard soko1_2.board support p 332 306 .north || decide (bonus 332 p ≤ bonus 306 p)) = true :=
  check_of_implication _ _ (bound946 p)
theorem guard947 (p : Pattern) (guard : pushGuard support p 332 306 280 280 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound947 (p : Pattern) (guard : pushGuard support p 332 306 280 280 = true) : bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some 280)) := by
  have certified := compare1005 p (guard947 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 306 (some 280))
  have normalized := agree0 _ _ (change_representative support p 306 (some 280) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check947 (p : Pattern) : (!pushGuard support p 332 306 280 280 || decide (bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some 280)))) = true :=
  check_of_implication _ _ (bound947 p)
theorem guard948 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 358 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound948 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 358 .south = true) : bonus 332 p ≤ bonus 358 p := by
  have certified := compare898 p (guard948 p guard)
  simpa only [at332, at358, Int.zero_add] using certified
theorem check948 (p : Pattern) : (!walkGuard soko1_2.board support p 332 358 .south || decide (bonus 332 p ≤ bonus 358 p)) = true :=
  check_of_implication _ _ (bound948 p)
theorem guard949 (p : Pattern) (guard : pushGuard support p 332 358 384 384 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound949 (p : Pattern) (guard : pushGuard support p 332 358 384 384 = true) : bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some 384)) := by
  have certified := compare1005 p (guard949 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 358 (some 384))
  have normalized := agree0 _ _ (change_representative support p 358 (some 384) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check949 (p : Pattern) : (!pushGuard support p 332 358 384 384 || decide (bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some 384)))) = true :=
  check_of_implication _ _ (bound949 p)
theorem guard950 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 333 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound950 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 333 .east = true) : bonus 332 p ≤ bonus 333 p := by
  have certified := compare898 p (guard950 p guard)
  simpa only [at332, at333, Int.zero_add] using certified
theorem check950 (p : Pattern) : (!walkGuard soko1_2.board support p 332 333 .east || decide (bonus 332 p ≤ bonus 333 p)) = true :=
  check_of_implication _ _ (bound950 p)
theorem guard951 (p : Pattern) (guard : pushGuard support p 332 333 334 334 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound951 (p : Pattern) (guard : pushGuard support p 332 333 334 334 = true) : bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder 334 - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some 334)) := by
  have certified := compare1005 p (guard951 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 333 (some 334))
  have normalized := agree0 _ _ (change_representative support p 333 (some 334) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check951 (p : Pattern) : (!pushGuard support p 332 333 334 334 || decide (bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder 334 - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some 334)))) = true :=
  check_of_implication _ _ (bound951 p)
theorem guard952 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 331 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound952 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 331 .west = true) : bonus 332 p ≤ bonus 331 p := by
  have certified := compare898 p (guard952 p guard)
  simpa only [at332, at331, Int.zero_add] using certified
theorem check952 (p : Pattern) : (!walkGuard soko1_2.board support p 332 331 .west || decide (bonus 332 p ≤ bonus 331 p)) = true :=
  check_of_implication _ _ (bound952 p)
theorem guard953 (p : Pattern) (guard : pushGuard support p 332 331 330 330 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound953 (p : Pattern) (guard : pushGuard support p 332 331 330 330 = true) : bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder 330 - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some 330)) := by
  have certified := compare1005 p (guard953 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 331 (some 330))
  have normalized := agree0 _ _ (change_representative support p 331 (some 330) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check953 (p : Pattern) : (!pushGuard support p 332 331 330 330 || decide (bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder 330 - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some 330)))) = true :=
  check_of_implication _ _ (bound953 p)
theorem guard954 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 307 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound954 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 307 .northEast = true) : bonus 332 p ≤ bonus 307 p := by
  have certified := compare898 p (guard954 p guard)
  simpa only [at332, at307, Int.zero_add] using certified
theorem check954 (p : Pattern) : (!walkGuard soko1_2.board support p 332 307 .northEast || decide (bonus 332 p ≤ bonus 307 p)) = true :=
  check_of_implication _ _ (bound954 p)
theorem guard955 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 305 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound955 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 305 .northWest = true) : bonus 332 p ≤ bonus 305 p := by
  have certified := compare898 p (guard955 p guard)
  simpa only [at332, at305, Int.zero_add] using certified
theorem check955 (p : Pattern) : (!walkGuard soko1_2.board support p 332 305 .northWest || decide (bonus 332 p ≤ bonus 305 p)) = true :=
  check_of_implication _ _ (bound955 p)
theorem guard956 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 359 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound956 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 359 .southEast = true) : bonus 332 p ≤ bonus 359 p := by
  have certified := compare898 p (guard956 p guard)
  simpa only [at332, at359, Int.zero_add] using certified
theorem check956 (p : Pattern) : (!walkGuard soko1_2.board support p 332 359 .southEast || decide (bonus 332 p ≤ bonus 359 p)) = true :=
  check_of_implication _ _ (bound956 p)
theorem guard957 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 357 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound957 (p : Pattern) (guard : walkGuard soko1_2.board support p 332 357 .southWest = true) : bonus 332 p ≤ bonus 357 p := by
  have certified := compare898 p (guard957 p guard)
  simpa only [at332, at357, Int.zero_add] using certified
theorem check957 (p : Pattern) : (!walkGuard soko1_2.board support p 332 357 .southWest || decide (bonus 332 p ≤ bonus 357 p)) = true :=
  check_of_implication _ _ (bound957 p)
theorem guard958 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 307 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound958 (p : Pattern) (guard : walkGuard soko1_2.board support p 333 307 .north = true) : bonus 333 p ≤ bonus 307 p := by
  have certified := compare898 p (guard958 p guard)
  simpa only [at333, at307, Int.zero_add] using certified
theorem check958 (p : Pattern) : (!walkGuard soko1_2.board support p 333 307 .north || decide (bonus 333 p ≤ bonus 307 p)) = true :=
  check_of_implication _ _ (bound958 p)
theorem guard959 (p : Pattern) (guard : pushGuard support p 333 307 281 281 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound959 (p : Pattern) (guard : pushGuard support p 333 307 281 281 = true) : bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder 281 - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some 281)) := by
  have certified := compare1005 p (guard959 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 307 (some 281))
  have normalized := agree0 _ _ (change_representative support p 307 (some 281) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check959 (p : Pattern) : (!pushGuard support p 333 307 281 281 || decide (bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder 281 - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some 281)))) = true :=
  check_of_implication _ _ (bound959 p)
end NetHack.Sokoban12CostPartition
