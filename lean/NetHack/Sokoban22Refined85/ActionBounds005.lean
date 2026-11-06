import NetHack.Sokoban22Refined85.ActionBounds004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard120 (p : Pattern) (guard : pushGuard support p 73 51 29 29 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound120 (p : Pattern) (guard : pushGuard support p 73 51 29 29 = true) : bonus 73 p ≤ 1 + Generated.soko2_2Potential.boulder 29 - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some 29)) := by
  have certified := compare20 p (guard120 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 51 (some 29))
  have normalized := agree312 _ _ (change_representative support p 51 (some 29) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check120 (p : Pattern) : (!pushGuard support p 73 51 29 29 || decide (bonus 73 p ≤ 1 + Generated.soko2_2Potential.boulder 29 - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some 29)))) = true :=
  check_of_implication _ _ (bound120 p)
theorem guard121 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 95 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound121 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 95 .south = true) : bonus 73 p ≤ bonus 95 p := by
  have certified := compare19 p (guard121 p guard)
  simpa only [at73, at95, Int.zero_add] using certified
theorem check121 (p : Pattern) : (!walkGuard soko2_2.board support p 73 95 .south || decide (bonus 73 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound121 p)
theorem guard122 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 74 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound122 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 74 .east = true) : bonus 73 p ≤ bonus 74 p := by
  have certified := compare19 p (guard122 p guard)
  simpa only [at73, at74, Int.zero_add] using certified
theorem check122 (p : Pattern) : (!walkGuard soko2_2.board support p 73 74 .east || decide (bonus 73 p ≤ bonus 74 p)) = true :=
  check_of_implication _ _ (bound122 p)
theorem guard123 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 52 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound123 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 52 .northEast = true) : bonus 73 p ≤ bonus 52 p := by
  have certified := compare19 p (guard123 p guard)
  simpa only [at73, at52, Int.zero_add] using certified
theorem check123 (p : Pattern) : (!walkGuard soko2_2.board support p 73 52 .northEast || decide (bonus 73 p ≤ bonus 52 p)) = true :=
  check_of_implication _ _ (bound123 p)
theorem guard124 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 50 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound124 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 50 .northWest = true) : bonus 73 p ≤ bonus 50 p := by
  have certified := compare19 p (guard124 p guard)
  simpa only [at73, at50, Int.zero_add] using certified
theorem check124 (p : Pattern) : (!walkGuard soko2_2.board support p 73 50 .northWest || decide (bonus 73 p ≤ bonus 50 p)) = true :=
  check_of_implication _ _ (bound124 p)
theorem guard125 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 96 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound125 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 96 .southEast = true) : bonus 73 p ≤ bonus 96 p := by
  have certified := compare19 p (guard125 p guard)
  simpa only [at73, at96, Int.zero_add] using certified
theorem check125 (p : Pattern) : (!walkGuard soko2_2.board support p 73 96 .southEast || decide (bonus 73 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound125 p)
theorem guard126 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 94 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound126 (p : Pattern) (guard : walkGuard soko2_2.board support p 73 94 .southWest = true) : bonus 73 p ≤ bonus 94 p := by
  have certified := compare19 p (guard126 p guard)
  simpa only [at73, at94, Int.zero_add] using certified
theorem check126 (p : Pattern) : (!walkGuard soko2_2.board support p 73 94 .southWest || decide (bonus 73 p ≤ bonus 94 p)) = true :=
  check_of_implication _ _ (bound126 p)
theorem guard127 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 52 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound127 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 52 .north = true) : bonus 74 p ≤ bonus 52 p := by
  have certified := compare19 p (guard127 p guard)
  simpa only [at74, at52, Int.zero_add] using certified
theorem check127 (p : Pattern) : (!walkGuard soko2_2.board support p 74 52 .north || decide (bonus 74 p ≤ bonus 52 p)) = true :=
  check_of_implication _ _ (bound127 p)
theorem guard128 (p : Pattern) (guard : pushGuard support p 74 52 30 30 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound128 (p : Pattern) (guard : pushGuard support p 74 52 30 30 = true) : bonus 74 p ≤ 1 + Generated.soko2_2Potential.boulder 30 - Generated.soko2_2Potential.boulder 52 + bonus 52 (change p 52 (some 30)) := by
  have certified := compare20 p (guard128 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 52 (some 30))
  have normalized := agree312 _ _ (change_representative support p 52 (some 30) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check128 (p : Pattern) : (!pushGuard support p 74 52 30 30 || decide (bonus 74 p ≤ 1 + Generated.soko2_2Potential.boulder 30 - Generated.soko2_2Potential.boulder 52 + bonus 52 (change p 52 (some 30)))) = true :=
  check_of_implication _ _ (bound128 p)
theorem guard129 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 96 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound129 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 96 .south = true) : bonus 74 p ≤ bonus 96 p := by
  have certified := compare19 p (guard129 p guard)
  simpa only [at74, at96, Int.zero_add] using certified
theorem check129 (p : Pattern) : (!walkGuard soko2_2.board support p 74 96 .south || decide (bonus 74 p ≤ bonus 96 p)) = true :=
  check_of_implication _ _ (bound129 p)
theorem guard130 (p : Pattern) (guard : pushGuard support p 74 96 118 118 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound130 (p : Pattern) (guard : pushGuard support p 74 96 118 118 = true) : bonus 74 p ≤ 1 + Generated.soko2_2Potential.boulder 118 - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some 118)) := by
  have certified := compare20 p (guard130 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 96 (some 118))
  have normalized := agree312 _ _ (change_representative support p 96 (some 118) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check130 (p : Pattern) : (!pushGuard support p 74 96 118 118 || decide (bonus 74 p ≤ 1 + Generated.soko2_2Potential.boulder 118 - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some 118)))) = true :=
  check_of_implication _ _ (bound130 p)
theorem guard131 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 73 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound131 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 73 .west = true) : bonus 74 p ≤ bonus 73 p := by
  have certified := compare19 p (guard131 p guard)
  simpa only [at74, at73, Int.zero_add] using certified
theorem check131 (p : Pattern) : (!walkGuard soko2_2.board support p 74 73 .west || decide (bonus 74 p ≤ bonus 73 p)) = true :=
  check_of_implication _ _ (bound131 p)
theorem guard132 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 51 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound132 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 51 .northWest = true) : bonus 74 p ≤ bonus 51 p := by
  have certified := compare19 p (guard132 p guard)
  simpa only [at74, at51, Int.zero_add] using certified
theorem check132 (p : Pattern) : (!walkGuard soko2_2.board support p 74 51 .northWest || decide (bonus 74 p ≤ bonus 51 p)) = true :=
  check_of_implication _ _ (bound132 p)
theorem guard133 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 97 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound133 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 97 .southEast = true) : bonus 74 p ≤ bonus 97 p := by
  have certified := compare19 p (guard133 p guard)
  simpa only [at74, at97, Int.zero_add] using certified
theorem check133 (p : Pattern) : (!walkGuard soko2_2.board support p 74 97 .southEast || decide (bonus 74 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound133 p)
theorem guard134 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 95 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound134 (p : Pattern) (guard : walkGuard soko2_2.board support p 74 95 .southWest = true) : bonus 74 p ≤ bonus 95 p := by
  have certified := compare19 p (guard134 p guard)
  simpa only [at74, at95, Int.zero_add] using certified
theorem check134 (p : Pattern) : (!walkGuard soko2_2.board support p 74 95 .southWest || decide (bonus 74 p ≤ bonus 95 p)) = true :=
  check_of_implication _ _ (bound134 p)
theorem guard135 (p : Pattern) (guard : walkGuard soko2_2.board support p 76 98 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound135 (p : Pattern) (guard : walkGuard soko2_2.board support p 76 98 .south = true) : bonus 76 p ≤ bonus 98 p := by
  have certified := compare19 p (guard135 p guard)
  simpa only [at76, at98, Int.zero_add] using certified
theorem check135 (p : Pattern) : (!walkGuard soko2_2.board support p 76 98 .south || decide (bonus 76 p ≤ bonus 98 p)) = true :=
  check_of_implication _ _ (bound135 p)
theorem guard136 (p : Pattern) (guard : pushGuard support p 76 98 120 120 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound136 (p : Pattern) (guard : pushGuard support p 76 98 120 120 = true) : bonus 76 p ≤ 1 + Generated.soko2_2Potential.boulder 120 - Generated.soko2_2Potential.boulder 98 + bonus 98 (change p 98 (some 120)) := by
  have certified := compare20 p (guard136 p guard)
  change d312 p ≤ (1 : Int) + d312 (change p 98 (some 120))
  have normalized := agree312 _ _ (change_representative support p 98 (some 120) 10000 dummy_outside)
  rw [normalized]
  change d312 p ≤ (1 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check136 (p : Pattern) : (!pushGuard support p 76 98 120 120 || decide (bonus 76 p ≤ 1 + Generated.soko2_2Potential.boulder 120 - Generated.soko2_2Potential.boulder 98 + bonus 98 (change p 98 (some 120)))) = true :=
  check_of_implication _ _ (bound136 p)
theorem guard137 (p : Pattern) (guard : walkGuard soko2_2.board support p 76 97 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound137 (p : Pattern) (guard : walkGuard soko2_2.board support p 76 97 .southWest = true) : bonus 76 p ≤ bonus 97 p := by
  have certified := compare19 p (guard137 p guard)
  simpa only [at76, at97, Int.zero_add] using certified
theorem check137 (p : Pattern) : (!walkGuard soko2_2.board support p 76 97 .southWest || decide (bonus 76 p ≤ bonus 97 p)) = true :=
  check_of_implication _ _ (bound137 p)
theorem guard138 (p : Pattern) (guard : walkGuard soko2_2.board support p 78 100 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound138 (p : Pattern) (guard : walkGuard soko2_2.board support p 78 100 .south = true) : bonus 78 p ≤ bonus 100 p := by
  have certified := compare1086 p (guard138 p guard)
  simpa only [at78, at100, Int.zero_add] using certified
theorem check138 (p : Pattern) : (!walkGuard soko2_2.board support p 78 100 .south || decide (bonus 78 p ≤ bonus 100 p)) = true :=
  check_of_implication _ _ (bound138 p)
theorem guard139 (p : Pattern) (guard : pushGuard support p 78 100 122 122 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound139 (p : Pattern) (guard : pushGuard support p 78 100 122 122 = true) : bonus 78 p ≤ 1 + Generated.soko2_2Potential.boulder 122 - Generated.soko2_2Potential.boulder 100 + bonus 100 (change p 100 (some 122)) := by
  have certified := compare1087 p (guard139 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 100 (some 122))
  have normalized := agree0 _ _ (change_representative support p 100 (some 122) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check139 (p : Pattern) : (!pushGuard support p 78 100 122 122 || decide (bonus 78 p ≤ 1 + Generated.soko2_2Potential.boulder 122 - Generated.soko2_2Potential.boulder 100 + bonus 100 (change p 100 (some 122)))) = true :=
  check_of_implication _ _ (bound139 p)
theorem guard140 (p : Pattern) (guard : walkGuard soko2_2.board support p 78 79 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound140 (p : Pattern) (guard : walkGuard soko2_2.board support p 78 79 .east = true) : bonus 78 p ≤ bonus 79 p := by
  have certified := compare1086 p (guard140 p guard)
  simpa only [at78, at79, Int.zero_add] using certified
theorem check140 (p : Pattern) : (!walkGuard soko2_2.board support p 78 79 .east || decide (bonus 78 p ≤ bonus 79 p)) = true :=
  check_of_implication _ _ (bound140 p)
theorem guard141 (p : Pattern) (guard : pushGuard support p 78 79 80 80 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound141 (p : Pattern) (guard : pushGuard support p 78 79 80 80 = true) : bonus 78 p ≤ 1 + Generated.soko2_2Potential.boulder 80 - Generated.soko2_2Potential.boulder 79 + bonus 79 (change p 79 (some 80)) := by
  have certified := compare1087 p (guard141 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 79 (some 80))
  have normalized := agree0 _ _ (change_representative support p 79 (some 80) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check141 (p : Pattern) : (!pushGuard support p 78 79 80 80 || decide (bonus 78 p ≤ 1 + Generated.soko2_2Potential.boulder 80 - Generated.soko2_2Potential.boulder 79 + bonus 79 (change p 79 (some 80)))) = true :=
  check_of_implication _ _ (bound141 p)
theorem guard142 (p : Pattern) (guard : walkGuard soko2_2.board support p 78 101 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound142 (p : Pattern) (guard : walkGuard soko2_2.board support p 78 101 .southEast = true) : bonus 78 p ≤ bonus 101 p := by
  have certified := compare1086 p (guard142 p guard)
  simpa only [at78, at101, Int.zero_add] using certified
theorem check142 (p : Pattern) : (!walkGuard soko2_2.board support p 78 101 .southEast || decide (bonus 78 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound142 p)
theorem guard143 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 101 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound143 (p : Pattern) (guard : walkGuard soko2_2.board support p 79 101 .south = true) : bonus 79 p ≤ bonus 101 p := by
  have certified := compare1086 p (guard143 p guard)
  simpa only [at79, at101, Int.zero_add] using certified
theorem check143 (p : Pattern) : (!walkGuard soko2_2.board support p 79 101 .south || decide (bonus 79 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound143 p)
end NetHack.Sokoban22Refined85
