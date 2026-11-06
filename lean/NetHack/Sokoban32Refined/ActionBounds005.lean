import NetHack.Sokoban32Refined.ActionBounds004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard120 (p : Pattern) (guard : pushGuard support p 61 60 59 59 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound120 (p : Pattern) (guard : pushGuard support p 61 60 59 59 = true) : bonus 61 p ≤ 1 + Generated.soko3_2Potential.boulder 59 - Generated.soko3_2Potential.boulder 60 + bonus 60 (change p 60 (some 59)) := by
  have certified := compare104 p (guard120 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 60 (some 59))
  have normalized := agree134 _ _ (change_representative support p 60 (some 59) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check120 (p : Pattern) : (!pushGuard support p 61 60 59 59 || decide (bonus 61 p ≤ 1 + Generated.soko3_2Potential.boulder 59 - Generated.soko3_2Potential.boulder 60 + bonus 60 (change p 60 (some 59)))) = true :=
  check_of_implication _ _ (bound120 p)
theorem guard121 (p : Pattern) (guard : walkGuard soko3_2.board support p 61 88 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound121 (p : Pattern) (guard : walkGuard soko3_2.board support p 61 88 .southEast = true) : bonus 61 p ≤ bonus 88 p := by
  have certified := compare0 p (guard121 p guard)
  simpa only [at61, at88, Int.zero_add] using certified
theorem check121 (p : Pattern) : (!walkGuard soko3_2.board support p 61 88 .southEast || decide (bonus 61 p ≤ bonus 88 p)) = true :=
  check_of_implication _ _ (bound121 p)
theorem guard122 (p : Pattern) (guard : walkGuard soko3_2.board support p 61 86 .southWest = true) : d833 p = 1 := by
  change (!false && !(p 86) && !(true && true && false)) = true at guard
  cases h86 : p 86
  all_goals simp [d0, d1, d833, h86] at guard ⊢
theorem bound122 (p : Pattern) (guard : walkGuard soko3_2.board support p 61 86 .southWest = true) : bonus 61 p ≤ bonus 86 p := by
  have certified := compare197 p (guard122 p guard)
  simpa only [at61, at86, Int.zero_add] using certified
theorem check122 (p : Pattern) : (!walkGuard soko3_2.board support p 61 86 .southWest || decide (bonus 61 p ≤ bonus 86 p)) = true :=
  check_of_implication _ _ (bound122 p)
theorem guard123 (p : Pattern) (guard : walkGuard soko3_2.board support p 62 88 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound123 (p : Pattern) (guard : walkGuard soko3_2.board support p 62 88 .south = true) : bonus 62 p ≤ bonus 88 p := by
  have certified := compare0 p (guard123 p guard)
  simpa only [at62, at88, Int.zero_add] using certified
theorem check123 (p : Pattern) : (!walkGuard soko3_2.board support p 62 88 .south || decide (bonus 62 p ≤ bonus 88 p)) = true :=
  check_of_implication _ _ (bound123 p)
theorem guard124 (p : Pattern) (guard : pushGuard support p 62 88 114 114 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound124 (p : Pattern) (guard : pushGuard support p 62 88 114 114 = true) : bonus 62 p ≤ 1 + Generated.soko3_2Potential.boulder 114 - Generated.soko3_2Potential.boulder 88 + bonus 88 (change p 88 (some 114)) := by
  have certified := compare104 p (guard124 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 88 (some 114))
  have normalized := agree134 _ _ (change_representative support p 88 (some 114) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check124 (p : Pattern) : (!pushGuard support p 62 88 114 114 || decide (bonus 62 p ≤ 1 + Generated.soko3_2Potential.boulder 114 - Generated.soko3_2Potential.boulder 88 + bonus 88 (change p 88 (some 114)))) = true :=
  check_of_implication _ _ (bound124 p)
theorem guard125 (p : Pattern) (guard : walkGuard soko3_2.board support p 62 61 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound125 (p : Pattern) (guard : walkGuard soko3_2.board support p 62 61 .west = true) : bonus 62 p ≤ bonus 61 p := by
  have certified := compare0 p (guard125 p guard)
  simpa only [at62, at61, Int.zero_add] using certified
theorem check125 (p : Pattern) : (!walkGuard soko3_2.board support p 62 61 .west || decide (bonus 62 p ≤ bonus 61 p)) = true :=
  check_of_implication _ _ (bound125 p)
theorem guard126 (p : Pattern) (guard : pushGuard support p 62 61 60 60 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound126 (p : Pattern) (guard : pushGuard support p 62 61 60 60 = true) : bonus 62 p ≤ 1 + Generated.soko3_2Potential.boulder 60 - Generated.soko3_2Potential.boulder 61 + bonus 61 (change p 61 (some 60)) := by
  have certified := compare104 p (guard126 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 61 (some 60))
  have normalized := agree134 _ _ (change_representative support p 61 (some 60) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check126 (p : Pattern) : (!pushGuard support p 62 61 60 60 || decide (bonus 62 p ≤ 1 + Generated.soko3_2Potential.boulder 60 - Generated.soko3_2Potential.boulder 61 + bonus 61 (change p 61 (some 60)))) = true :=
  check_of_implication _ _ (bound126 p)
theorem guard127 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 42 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound127 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 42 .north = true) : bonus 68 p ≤ bonus 42 p := by
  have certified := compare103 p (guard127 p guard)
  simpa only [at68, at42, Int.zero_add] using certified
theorem check127 (p : Pattern) : (!walkGuard soko3_2.board support p 68 42 .north || decide (bonus 68 p ≤ bonus 42 p)) = true :=
  check_of_implication _ _ (bound127 p)
theorem guard128 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 94 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound128 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 94 .south = true) : bonus 68 p ≤ bonus 94 p := by
  have certified := compare103 p (guard128 p guard)
  simpa only [at68, at94, Int.zero_add] using certified
theorem check128 (p : Pattern) : (!walkGuard soko3_2.board support p 68 94 .south || decide (bonus 68 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound128 p)
theorem guard129 (p : Pattern) (guard : pushGuard support p 68 94 120 120 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound129 (p : Pattern) (guard : pushGuard support p 68 94 120 120 = true) : bonus 68 p ≤ 1 + Generated.soko3_2Potential.boulder 120 - Generated.soko3_2Potential.boulder 94 + bonus 94 (change p 94 (some 120)) := by
  have certified := compare37 p (guard129 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 94 (some 120))
  have normalized := agree0 _ _ (change_representative support p 94 (some 120) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check129 (p : Pattern) : (!pushGuard support p 68 94 120 120 || decide (bonus 68 p ≤ 1 + Generated.soko3_2Potential.boulder 120 - Generated.soko3_2Potential.boulder 94 + bonus 94 (change p 94 (some 120)))) = true :=
  check_of_implication _ _ (bound129 p)
theorem guard130 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 69 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound130 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 69 .east = true) : bonus 68 p ≤ bonus 69 p := by
  have certified := compare103 p (guard130 p guard)
  simpa only [at68, at69, Int.zero_add] using certified
theorem check130 (p : Pattern) : (!walkGuard soko3_2.board support p 68 69 .east || decide (bonus 68 p ≤ bonus 69 p)) = true :=
  check_of_implication _ _ (bound130 p)
theorem guard131 (p : Pattern) (guard : pushGuard support p 68 69 70 70 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound131 (p : Pattern) (guard : pushGuard support p 68 69 70 70 = true) : bonus 68 p ≤ 1 + Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some 70)) := by
  have certified := compare37 p (guard131 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 69 (some 70))
  have normalized := agree0 _ _ (change_representative support p 69 (some 70) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check131 (p : Pattern) : (!pushGuard support p 68 69 70 70 || decide (bonus 68 p ≤ 1 + Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some 70)))) = true :=
  check_of_implication _ _ (bound131 p)
theorem guard132 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 43 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound132 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 43 .northEast = true) : bonus 68 p ≤ bonus 43 p := by
  have certified := compare103 p (guard132 p guard)
  simpa only [at68, at43, Int.zero_add] using certified
theorem check132 (p : Pattern) : (!walkGuard soko3_2.board support p 68 43 .northEast || decide (bonus 68 p ≤ bonus 43 p)) = true :=
  check_of_implication _ _ (bound132 p)
theorem guard133 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 95 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound133 (p : Pattern) (guard : walkGuard soko3_2.board support p 68 95 .southEast = true) : bonus 68 p ≤ bonus 95 p := by
  have certified := compare103 p (guard133 p guard)
  simpa only [at68, at95, Int.zero_add] using certified
theorem check133 (p : Pattern) : (!walkGuard soko3_2.board support p 68 95 .southEast || decide (bonus 68 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound133 p)
theorem guard134 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 43 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound134 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 43 .north = true) : bonus 69 p ≤ bonus 43 p := by
  have certified := compare103 p (guard134 p guard)
  simpa only [at69, at43, Int.zero_add] using certified
theorem check134 (p : Pattern) : (!walkGuard soko3_2.board support p 69 43 .north || decide (bonus 69 p ≤ bonus 43 p)) = true :=
  check_of_implication _ _ (bound134 p)
theorem guard135 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 95 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound135 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 95 .south = true) : bonus 69 p ≤ bonus 95 p := by
  have certified := compare103 p (guard135 p guard)
  simpa only [at69, at95, Int.zero_add] using certified
theorem check135 (p : Pattern) : (!walkGuard soko3_2.board support p 69 95 .south || decide (bonus 69 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound135 p)
theorem guard136 (p : Pattern) (guard : pushGuard support p 69 95 121 121 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound136 (p : Pattern) (guard : pushGuard support p 69 95 121 121 = true) : bonus 69 p ≤ 1 + Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some 121)) := by
  have certified := compare37 p (guard136 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 95 (some 121))
  have normalized := agree0 _ _ (change_representative support p 95 (some 121) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check136 (p : Pattern) : (!pushGuard support p 69 95 121 121 || decide (bonus 69 p ≤ 1 + Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some 121)))) = true :=
  check_of_implication _ _ (bound136 p)
theorem guard137 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 70 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound137 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 70 .east = true) : bonus 69 p ≤ bonus 70 p := by
  have certified := compare103 p (guard137 p guard)
  simpa only [at69, at70, Int.zero_add] using certified
theorem check137 (p : Pattern) : (!walkGuard soko3_2.board support p 69 70 .east || decide (bonus 69 p ≤ bonus 70 p)) = true :=
  check_of_implication _ _ (bound137 p)
theorem guard138 (p : Pattern) (guard : pushGuard support p 69 70 71 71 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound138 (p : Pattern) (guard : pushGuard support p 69 70 71 71 = true) : bonus 69 p ≤ 1 + Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some 71)) := by
  have certified := compare37 p (guard138 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 70 (some 71))
  have normalized := agree0 _ _ (change_representative support p 70 (some 71) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check138 (p : Pattern) : (!pushGuard support p 69 70 71 71 || decide (bonus 69 p ≤ 1 + Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some 71)))) = true :=
  check_of_implication _ _ (bound138 p)
theorem guard139 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 68 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound139 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 68 .west = true) : bonus 69 p ≤ bonus 68 p := by
  have certified := compare103 p (guard139 p guard)
  simpa only [at69, at68, Int.zero_add] using certified
theorem check139 (p : Pattern) : (!walkGuard soko3_2.board support p 69 68 .west || decide (bonus 69 p ≤ bonus 68 p)) = true :=
  check_of_implication _ _ (bound139 p)
theorem guard140 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 44 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound140 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 44 .northEast = true) : bonus 69 p ≤ bonus 44 p := by
  have certified := compare103 p (guard140 p guard)
  simpa only [at69, at44, Int.zero_add] using certified
theorem check140 (p : Pattern) : (!walkGuard soko3_2.board support p 69 44 .northEast || decide (bonus 69 p ≤ bonus 44 p)) = true :=
  check_of_implication _ _ (bound140 p)
theorem guard141 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 42 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound141 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 42 .northWest = true) : bonus 69 p ≤ bonus 42 p := by
  have certified := compare103 p (guard141 p guard)
  simpa only [at69, at42, Int.zero_add] using certified
theorem check141 (p : Pattern) : (!walkGuard soko3_2.board support p 69 42 .northWest || decide (bonus 69 p ≤ bonus 42 p)) = true :=
  check_of_implication _ _ (bound141 p)
theorem guard142 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 96 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound142 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 96 .southEast = true) : bonus 69 p ≤ bonus 96 p := by
  have certified := compare103 p (guard142 p guard)
  simpa only [at69, at96, Int.zero_add] using certified
theorem check142 (p : Pattern) : (!walkGuard soko3_2.board support p 69 96 .southEast || decide (bonus 69 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound142 p)
theorem guard143 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 94 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound143 (p : Pattern) (guard : walkGuard soko3_2.board support p 69 94 .southWest = true) : bonus 69 p ≤ bonus 94 p := by
  have certified := compare103 p (guard143 p guard)
  simpa only [at69, at94, Int.zero_add] using certified
theorem check143 (p : Pattern) : (!walkGuard soko3_2.board support p 69 94 .southWest || decide (bonus 69 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound143 p)
end NetHack.Sokoban32Refined
