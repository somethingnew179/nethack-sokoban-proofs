import NetHack.Sokoban12CostPartition.ActionBounds037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard912 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 320 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound912 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 320 .east = true) : bonus 319 p ≤ bonus 320 p := by
  have certified := compare897 p (guard912 p guard)
  simpa only [at319, at320, Int.zero_add] using certified
theorem check912 (p : Pattern) : (!walkGuard soko1_2.board support p 319 320 .east || decide (bonus 319 p ≤ bonus 320 p)) = true :=
  check_of_implication _ _ (bound912 p)
theorem guard913 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 318 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound913 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 318 .west = true) : bonus 319 p ≤ bonus 318 p := by
  have certified := compare897 p (guard913 p guard)
  simpa only [at319, at318, Int.zero_add] using certified
theorem check913 (p : Pattern) : (!walkGuard soko1_2.board support p 319 318 .west || decide (bonus 319 p ≤ bonus 318 p)) = true :=
  check_of_implication _ _ (bound913 p)
theorem guard914 (p : Pattern) (guard : pushGuard support p 319 318 317 317 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound914 (p : Pattern) (guard : pushGuard support p 319 318 317 317 = true) : bonus 319 p ≤ 1 + Generated.soko1_2Potential.boulder 317 - Generated.soko1_2Potential.boulder 318 + bonus 318 (change p 318 (some 317)) := by
  have certified := compare6292 p (guard914 p guard)
  change d258 p ≤ (3 : Int) + d258 (change p 318 (some 317))
  have normalized := agree258 _ _ (change_representative support p 318 (some 317) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (3 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check914 (p : Pattern) : (!pushGuard support p 319 318 317 317 || decide (bonus 319 p ≤ 1 + Generated.soko1_2Potential.boulder 317 - Generated.soko1_2Potential.boulder 318 + bonus 318 (change p 318 (some 317)))) = true :=
  check_of_implication _ _ (bound914 p)
theorem guard915 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 294 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound915 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 294 .northEast = true) : bonus 319 p ≤ bonus 294 p := by
  have certified := compare897 p (guard915 p guard)
  simpa only [at319, at294, Int.zero_add] using certified
theorem check915 (p : Pattern) : (!walkGuard soko1_2.board support p 319 294 .northEast || decide (bonus 319 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound915 p)
theorem guard916 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 292 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound916 (p : Pattern) (guard : walkGuard soko1_2.board support p 319 292 .northWest = true) : bonus 319 p ≤ bonus 292 p := by
  have certified := compare897 p (guard916 p guard)
  simpa only [at319, at292, Int.zero_add] using certified
theorem check916 (p : Pattern) : (!walkGuard soko1_2.board support p 319 292 .northWest || decide (bonus 319 p ≤ bonus 292 p)) = true :=
  check_of_implication _ _ (bound916 p)
theorem guard917 (p : Pattern) (guard : walkGuard soko1_2.board support p 320 294 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound917 (p : Pattern) (guard : walkGuard soko1_2.board support p 320 294 .north = true) : bonus 320 p ≤ bonus 294 p := by
  have certified := compare897 p (guard917 p guard)
  simpa only [at320, at294, Int.zero_add] using certified
theorem check917 (p : Pattern) : (!walkGuard soko1_2.board support p 320 294 .north || decide (bonus 320 p ≤ bonus 294 p)) = true :=
  check_of_implication _ _ (bound917 p)
theorem guard918 (p : Pattern) (guard : walkGuard soko1_2.board support p 320 319 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound918 (p : Pattern) (guard : walkGuard soko1_2.board support p 320 319 .west = true) : bonus 320 p ≤ bonus 319 p := by
  have certified := compare897 p (guard918 p guard)
  simpa only [at320, at319, Int.zero_add] using certified
theorem check918 (p : Pattern) : (!walkGuard soko1_2.board support p 320 319 .west || decide (bonus 320 p ≤ bonus 319 p)) = true :=
  check_of_implication _ _ (bound918 p)
theorem guard919 (p : Pattern) (guard : pushGuard support p 320 319 318 318 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound919 (p : Pattern) (guard : pushGuard support p 320 319 318 318 = true) : bonus 320 p ≤ 1 + Generated.soko1_2Potential.boulder 318 - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some 318)) := by
  have certified := compare2570 p (guard919 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 319 (some 318))
  have normalized := agree258 _ _ (change_representative support p 319 (some 318) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check919 (p : Pattern) : (!pushGuard support p 320 319 318 318 || decide (bonus 320 p ≤ 1 + Generated.soko1_2Potential.boulder 318 - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some 318)))) = true :=
  check_of_implication _ _ (bound919 p)
theorem guard920 (p : Pattern) (guard : walkGuard soko1_2.board support p 320 293 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound920 (p : Pattern) (guard : walkGuard soko1_2.board support p 320 293 .northWest = true) : bonus 320 p ≤ bonus 293 p := by
  have certified := compare897 p (guard920 p guard)
  simpa only [at320, at293, Int.zero_add] using certified
theorem check920 (p : Pattern) : (!walkGuard soko1_2.board support p 320 293 .northWest || decide (bonus 320 p ≤ bonus 293 p)) = true :=
  check_of_implication _ _ (bound920 p)
theorem guard921 (p : Pattern) (guard : walkGuard soko1_2.board support p 320 345 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound921 (p : Pattern) (guard : walkGuard soko1_2.board support p 320 345 .southWest = true) : bonus 320 p ≤ bonus 345 p := by
  have certified := compare897 p (guard921 p guard)
  simpa only [at320, at345, Int.zero_add] using certified
theorem check921 (p : Pattern) : (!walkGuard soko1_2.board support p 320 345 .southWest || decide (bonus 320 p ≤ bonus 345 p)) = true :=
  check_of_implication _ _ (bound921 p)
theorem guard922 (p : Pattern) (guard : walkGuard soko1_2.board support p 322 296 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound922 (p : Pattern) (guard : walkGuard soko1_2.board support p 322 296 .north = true) : bonus 322 p ≤ bonus 296 p := by
  have certified := compare897 p (guard922 p guard)
  simpa only [at322, at296, Int.zero_add] using certified
theorem check922 (p : Pattern) : (!walkGuard soko1_2.board support p 322 296 .north || decide (bonus 322 p ≤ bonus 296 p)) = true :=
  check_of_implication _ _ (bound922 p)
theorem guard923 (p : Pattern) (guard : pushGuard support p 322 296 270 270 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound923 (p : Pattern) (guard : pushGuard support p 322 296 270 270 = true) : bonus 322 p ≤ 1 + Generated.soko1_2Potential.boulder 270 - Generated.soko1_2Potential.boulder 296 + bonus 296 (change p 296 (some 270)) := by
  have certified := compare5431 p (guard923 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 296 (some 270))
  have normalized := agree258 _ _ (change_representative support p 296 (some 270) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check923 (p : Pattern) : (!pushGuard support p 322 296 270 270 || decide (bonus 322 p ≤ 1 + Generated.soko1_2Potential.boulder 270 - Generated.soko1_2Potential.boulder 296 + bonus 296 (change p 296 (some 270)))) = true :=
  check_of_implication _ _ (bound923 p)
theorem guard924 (p : Pattern) (guard : walkGuard soko1_2.board support p 322 348 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound924 (p : Pattern) (guard : walkGuard soko1_2.board support p 322 348 .south = true) : bonus 322 p ≤ bonus 348 p := by
  have certified := compare897 p (guard924 p guard)
  simpa only [at322, at348, Int.zero_add] using certified
theorem check924 (p : Pattern) : (!walkGuard soko1_2.board support p 322 348 .south || decide (bonus 322 p ≤ bonus 348 p)) = true :=
  check_of_implication _ _ (bound924 p)
theorem guard925 (p : Pattern) (guard : pushGuard support p 322 348 374 374 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound925 (p : Pattern) (guard : pushGuard support p 322 348 374 374 = true) : bonus 322 p ≤ 1 + Generated.soko1_2Potential.boulder 374 - Generated.soko1_2Potential.boulder 348 + bonus 348 (change p 348 (some 374)) := by
  have certified := compare5431 p (guard925 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 348 (some 374))
  have normalized := agree258 _ _ (change_representative support p 348 (some 374) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check925 (p : Pattern) : (!pushGuard support p 322 348 374 374 || decide (bonus 322 p ≤ 1 + Generated.soko1_2Potential.boulder 374 - Generated.soko1_2Potential.boulder 348 + bonus 348 (change p 348 (some 374)))) = true :=
  check_of_implication _ _ (bound925 p)
theorem guard926 (p : Pattern) (guard : walkGuard soko1_2.board support p 322 297 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound926 (p : Pattern) (guard : walkGuard soko1_2.board support p 322 297 .northEast = true) : bonus 322 p ≤ bonus 297 p := by
  have certified := compare897 p (guard926 p guard)
  simpa only [at322, at297, Int.zero_add] using certified
theorem check926 (p : Pattern) : (!walkGuard soko1_2.board support p 322 297 .northEast || decide (bonus 322 p ≤ bonus 297 p)) = true :=
  check_of_implication _ _ (bound926 p)
theorem guard927 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 304 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound927 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 304 .north = true) : bonus 330 p ≤ bonus 304 p := by
  have certified := compare898 p (guard927 p guard)
  simpa only [at330, at304, Int.zero_add] using certified
theorem check927 (p : Pattern) : (!walkGuard soko1_2.board support p 330 304 .north || decide (bonus 330 p ≤ bonus 304 p)) = true :=
  check_of_implication _ _ (bound927 p)
theorem guard928 (p : Pattern) (guard : pushGuard support p 330 304 278 278 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound928 (p : Pattern) (guard : pushGuard support p 330 304 278 278 = true) : bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder 278 - Generated.soko1_2Potential.boulder 304 + bonus 304 (change p 304 (some 278)) := by
  have certified := compare1005 p (guard928 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 304 (some 278))
  have normalized := agree0 _ _ (change_representative support p 304 (some 278) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check928 (p : Pattern) : (!pushGuard support p 330 304 278 278 || decide (bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder 278 - Generated.soko1_2Potential.boulder 304 + bonus 304 (change p 304 (some 278)))) = true :=
  check_of_implication _ _ (bound928 p)
theorem guard929 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 356 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound929 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 356 .south = true) : bonus 330 p ≤ bonus 356 p := by
  have certified := compare898 p (guard929 p guard)
  simpa only [at330, at356, Int.zero_add] using certified
theorem check929 (p : Pattern) : (!walkGuard soko1_2.board support p 330 356 .south || decide (bonus 330 p ≤ bonus 356 p)) = true :=
  check_of_implication _ _ (bound929 p)
theorem guard930 (p : Pattern) (guard : pushGuard support p 330 356 382 382 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound930 (p : Pattern) (guard : pushGuard support p 330 356 382 382 = true) : bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder 382 - Generated.soko1_2Potential.boulder 356 + bonus 356 (change p 356 (some 382)) := by
  have certified := compare1005 p (guard930 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 356 (some 382))
  have normalized := agree0 _ _ (change_representative support p 356 (some 382) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check930 (p : Pattern) : (!pushGuard support p 330 356 382 382 || decide (bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder 382 - Generated.soko1_2Potential.boulder 356 + bonus 356 (change p 356 (some 382)))) = true :=
  check_of_implication _ _ (bound930 p)
theorem guard931 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 331 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound931 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 331 .east = true) : bonus 330 p ≤ bonus 331 p := by
  have certified := compare898 p (guard931 p guard)
  simpa only [at330, at331, Int.zero_add] using certified
theorem check931 (p : Pattern) : (!walkGuard soko1_2.board support p 330 331 .east || decide (bonus 330 p ≤ bonus 331 p)) = true :=
  check_of_implication _ _ (bound931 p)
theorem guard932 (p : Pattern) (guard : pushGuard support p 330 331 332 332 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound932 (p : Pattern) (guard : pushGuard support p 330 331 332 332 = true) : bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some 332)) := by
  have certified := compare1005 p (guard932 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 331 (some 332))
  have normalized := agree0 _ _ (change_representative support p 331 (some 332) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check932 (p : Pattern) : (!pushGuard support p 330 331 332 332 || decide (bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some 332)))) = true :=
  check_of_implication _ _ (bound932 p)
theorem guard933 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 305 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound933 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 305 .northEast = true) : bonus 330 p ≤ bonus 305 p := by
  have certified := compare898 p (guard933 p guard)
  simpa only [at330, at305, Int.zero_add] using certified
theorem check933 (p : Pattern) : (!walkGuard soko1_2.board support p 330 305 .northEast || decide (bonus 330 p ≤ bonus 305 p)) = true :=
  check_of_implication _ _ (bound933 p)
theorem guard934 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 357 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound934 (p : Pattern) (guard : walkGuard soko1_2.board support p 330 357 .southEast = true) : bonus 330 p ≤ bonus 357 p := by
  have certified := compare898 p (guard934 p guard)
  simpa only [at330, at357, Int.zero_add] using certified
theorem check934 (p : Pattern) : (!walkGuard soko1_2.board support p 330 357 .southEast || decide (bonus 330 p ≤ bonus 357 p)) = true :=
  check_of_implication _ _ (bound934 p)
theorem guard935 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 305 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound935 (p : Pattern) (guard : walkGuard soko1_2.board support p 331 305 .north = true) : bonus 331 p ≤ bonus 305 p := by
  have certified := compare898 p (guard935 p guard)
  simpa only [at331, at305, Int.zero_add] using certified
theorem check935 (p : Pattern) : (!walkGuard soko1_2.board support p 331 305 .north || decide (bonus 331 p ≤ bonus 305 p)) = true :=
  check_of_implication _ _ (bound935 p)
end NetHack.Sokoban12CostPartition
