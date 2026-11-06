import NetHack.Sokoban32Refined.ActionBounds010
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard264 (p : Pattern) (guard : pushGuard support p 96 97 98 98 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound264 (p : Pattern) (guard : pushGuard support p 96 97 98 98 = true) : bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some 98)) := by
  have certified := compare37 p (guard264 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 97 (some 98))
  have normalized := agree0 _ _ (change_representative support p 97 (some 98) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check264 (p : Pattern) : (!pushGuard support p 96 97 98 98 || decide (bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some 98)))) = true :=
  check_of_implication _ _ (bound264 p)
theorem guard265 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 95 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound265 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 95 .west = true) : bonus 96 p ≤ bonus 95 p := by
  have certified := compare103 p (guard265 p guard)
  simpa only [at96, at95, Int.zero_add] using certified
theorem check265 (p : Pattern) : (!walkGuard soko3_2.board support p 96 95 .west || decide (bonus 96 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound265 p)
theorem guard266 (p : Pattern) (guard : pushGuard support p 96 95 94 94 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound266 (p : Pattern) (guard : pushGuard support p 96 95 94 94 = true) : bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder 94 - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some 94)) := by
  have certified := compare37 p (guard266 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 95 (some 94))
  have normalized := agree0 _ _ (change_representative support p 95 (some 94) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check266 (p : Pattern) : (!pushGuard support p 96 95 94 94 || decide (bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder 94 - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some 94)))) = true :=
  check_of_implication _ _ (bound266 p)
theorem guard267 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 71 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound267 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 71 .northEast = true) : bonus 96 p ≤ bonus 71 p := by
  have certified := compare103 p (guard267 p guard)
  simpa only [at96, at71, Int.zero_add] using certified
theorem check267 (p : Pattern) : (!walkGuard soko3_2.board support p 96 71 .northEast || decide (bonus 96 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound267 p)
theorem guard268 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 69 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound268 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 69 .northWest = true) : bonus 96 p ≤ bonus 69 p := by
  have certified := compare103 p (guard268 p guard)
  simpa only [at96, at69, Int.zero_add] using certified
theorem check268 (p : Pattern) : (!walkGuard soko3_2.board support p 96 69 .northWest || decide (bonus 96 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound268 p)
theorem guard269 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 123 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound269 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 123 .southEast = true) : bonus 96 p ≤ bonus 123 p := by
  have certified := compare103 p (guard269 p guard)
  simpa only [at96, at123, Int.zero_add] using certified
theorem check269 (p : Pattern) : (!walkGuard soko3_2.board support p 96 123 .southEast || decide (bonus 96 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound269 p)
theorem guard270 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 121 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound270 (p : Pattern) (guard : walkGuard soko3_2.board support p 96 121 .southWest = true) : bonus 96 p ≤ bonus 121 p := by
  have certified := compare103 p (guard270 p guard)
  simpa only [at96, at121, Int.zero_add] using certified
theorem check270 (p : Pattern) : (!walkGuard soko3_2.board support p 96 121 .southWest || decide (bonus 96 p ≤ bonus 121 p)) = true :=
  check_of_implication _ _ (bound270 p)
theorem guard271 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 71 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound271 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 71 .north = true) : bonus 97 p ≤ bonus 71 p := by
  have certified := compare103 p (guard271 p guard)
  simpa only [at97, at71, Int.zero_add] using certified
theorem check271 (p : Pattern) : (!walkGuard soko3_2.board support p 97 71 .north || decide (bonus 97 p ≤ bonus 71 p)) = true :=
  check_of_implication _ _ (bound271 p)
theorem guard272 (p : Pattern) (guard : pushGuard support p 97 71 45 45 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound272 (p : Pattern) (guard : pushGuard support p 97 71 45 45 = true) : bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder 45 - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some 45)) := by
  have certified := compare37 p (guard272 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 71 (some 45))
  have normalized := agree0 _ _ (change_representative support p 71 (some 45) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check272 (p : Pattern) : (!pushGuard support p 97 71 45 45 || decide (bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder 45 - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some 45)))) = true :=
  check_of_implication _ _ (bound272 p)
theorem guard273 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 123 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound273 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 123 .south = true) : bonus 97 p ≤ bonus 123 p := by
  have certified := compare103 p (guard273 p guard)
  simpa only [at97, at123, Int.zero_add] using certified
theorem check273 (p : Pattern) : (!walkGuard soko3_2.board support p 97 123 .south || decide (bonus 97 p ≤ bonus 123 p)) = true :=
  check_of_implication _ _ (bound273 p)
theorem guard274 (p : Pattern) (guard : pushGuard support p 97 123 149 149 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound274 (p : Pattern) (guard : pushGuard support p 97 123 149 149 = true) : bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some 149)) := by
  have certified := compare37 p (guard274 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 123 (some 149))
  have normalized := agree0 _ _ (change_representative support p 123 (some 149) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check274 (p : Pattern) : (!pushGuard support p 97 123 149 149 || decide (bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some 149)))) = true :=
  check_of_implication _ _ (bound274 p)
theorem guard275 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 98 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound275 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 98 .east = true) : bonus 97 p ≤ bonus 98 p := by
  have certified := compare103 p (guard275 p guard)
  simpa only [at97, at98, Int.zero_add] using certified
theorem check275 (p : Pattern) : (!walkGuard soko3_2.board support p 97 98 .east || decide (bonus 97 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound275 p)
theorem guard276 (p : Pattern) (guard : pushGuard support p 97 98 99 99 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound276 (p : Pattern) (guard : pushGuard support p 97 98 99 99 = true) : bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some 99)) := by
  have certified := compare37 p (guard276 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 98 (some 99))
  have normalized := agree0 _ _ (change_representative support p 98 (some 99) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check276 (p : Pattern) : (!pushGuard support p 97 98 99 99 || decide (bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some 99)))) = true :=
  check_of_implication _ _ (bound276 p)
theorem guard277 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 96 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound277 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 96 .west = true) : bonus 97 p ≤ bonus 96 p := by
  have certified := compare103 p (guard277 p guard)
  simpa only [at97, at96, Int.zero_add] using certified
theorem check277 (p : Pattern) : (!walkGuard soko3_2.board support p 97 96 .west || decide (bonus 97 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound277 p)
theorem guard278 (p : Pattern) (guard : pushGuard support p 97 96 95 95 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound278 (p : Pattern) (guard : pushGuard support p 97 96 95 95 = true) : bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some 95)) := by
  have certified := compare37 p (guard278 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 96 (some 95))
  have normalized := agree0 _ _ (change_representative support p 96 (some 95) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check278 (p : Pattern) : (!pushGuard support p 97 96 95 95 || decide (bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some 95)))) = true :=
  check_of_implication _ _ (bound278 p)
theorem guard279 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 72 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound279 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 72 .northEast = true) : bonus 97 p ≤ bonus 72 p := by
  have certified := compare103 p (guard279 p guard)
  simpa only [at97, at72, Int.zero_add] using certified
theorem check279 (p : Pattern) : (!walkGuard soko3_2.board support p 97 72 .northEast || decide (bonus 97 p ≤ bonus 72 p)) = true :=
  check_of_implication _ _ (bound279 p)
theorem guard280 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 70 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound280 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 70 .northWest = true) : bonus 97 p ≤ bonus 70 p := by
  have certified := compare103 p (guard280 p guard)
  simpa only [at97, at70, Int.zero_add] using certified
theorem check280 (p : Pattern) : (!walkGuard soko3_2.board support p 97 70 .northWest || decide (bonus 97 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound280 p)
theorem guard281 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 124 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound281 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 124 .southEast = true) : bonus 97 p ≤ bonus 124 p := by
  have certified := compare103 p (guard281 p guard)
  simpa only [at97, at124, Int.zero_add] using certified
theorem check281 (p : Pattern) : (!walkGuard soko3_2.board support p 97 124 .southEast || decide (bonus 97 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound281 p)
theorem guard282 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 122 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound282 (p : Pattern) (guard : walkGuard soko3_2.board support p 97 122 .southWest = true) : bonus 97 p ≤ bonus 122 p := by
  have certified := compare103 p (guard282 p guard)
  simpa only [at97, at122, Int.zero_add] using certified
theorem check282 (p : Pattern) : (!walkGuard soko3_2.board support p 97 122 .southWest || decide (bonus 97 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound282 p)
theorem guard283 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 72 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound283 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 72 .north = true) : bonus 98 p ≤ bonus 72 p := by
  have certified := compare103 p (guard283 p guard)
  simpa only [at98, at72, Int.zero_add] using certified
theorem check283 (p : Pattern) : (!walkGuard soko3_2.board support p 98 72 .north || decide (bonus 98 p ≤ bonus 72 p)) = true :=
  check_of_implication _ _ (bound283 p)
theorem guard284 (p : Pattern) (guard : pushGuard support p 98 72 46 46 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound284 (p : Pattern) (guard : pushGuard support p 98 72 46 46 = true) : bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder 46 - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some 46)) := by
  have certified := compare37 p (guard284 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 72 (some 46))
  have normalized := agree0 _ _ (change_representative support p 72 (some 46) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check284 (p : Pattern) : (!pushGuard support p 98 72 46 46 || decide (bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder 46 - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some 46)))) = true :=
  check_of_implication _ _ (bound284 p)
theorem guard285 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 124 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound285 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 124 .south = true) : bonus 98 p ≤ bonus 124 p := by
  have certified := compare103 p (guard285 p guard)
  simpa only [at98, at124, Int.zero_add] using certified
theorem check285 (p : Pattern) : (!walkGuard soko3_2.board support p 98 124 .south || decide (bonus 98 p ≤ bonus 124 p)) = true :=
  check_of_implication _ _ (bound285 p)
theorem guard286 (p : Pattern) (guard : pushGuard support p 98 124 150 150 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound286 (p : Pattern) (guard : pushGuard support p 98 124 150 150 = true) : bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some 150)) := by
  have certified := compare37 p (guard286 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 124 (some 150))
  have normalized := agree0 _ _ (change_representative support p 124 (some 150) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check286 (p : Pattern) : (!pushGuard support p 98 124 150 150 || decide (bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some 150)))) = true :=
  check_of_implication _ _ (bound286 p)
theorem guard287 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 99 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound287 (p : Pattern) (guard : walkGuard soko3_2.board support p 98 99 .east = true) : bonus 98 p ≤ bonus 99 p := by
  have certified := compare103 p (guard287 p guard)
  simpa only [at98, at99, Int.zero_add] using certified
theorem check287 (p : Pattern) : (!walkGuard soko3_2.board support p 98 99 .east || decide (bonus 98 p ≤ bonus 99 p)) = true :=
  check_of_implication _ _ (bound287 p)
end NetHack.Sokoban32Refined
