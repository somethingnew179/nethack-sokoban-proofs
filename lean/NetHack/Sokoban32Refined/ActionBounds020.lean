import NetHack.Sokoban32Refined.ActionBounds019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard480 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 102 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound480 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 102 .north = true) : bonus 128 p ≤ bonus 102 p := by
  have certified := compare103 p (guard480 p guard)
  simpa only [at128, at102, Int.zero_add] using certified
theorem check480 (p : Pattern) : (!walkGuard soko3_2.board support p 128 102 .north || decide (bonus 128 p ≤ bonus 102 p)) = true :=
  check_of_implication _ _ (bound480 p)
theorem guard481 (p : Pattern) (guard : pushGuard support p 128 102 76 76 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound481 (p : Pattern) (guard : pushGuard support p 128 102 76 76 = true) : bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder 76 - Generated.soko3_2Potential.boulder 102 + bonus 102 (change p 102 (some 76)) := by
  have certified := compare37 p (guard481 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 102 (some 76))
  have normalized := agree0 _ _ (change_representative support p 102 (some 76) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check481 (p : Pattern) : (!pushGuard support p 128 102 76 76 || decide (bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder 76 - Generated.soko3_2Potential.boulder 102 + bonus 102 (change p 102 (some 76)))) = true :=
  check_of_implication _ _ (bound481 p)
theorem guard482 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 154 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound482 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 154 .south = true) : bonus 128 p ≤ bonus 154 p := by
  have certified := compare103 p (guard482 p guard)
  simpa only [at128, at154, Int.zero_add] using certified
theorem check482 (p : Pattern) : (!walkGuard soko3_2.board support p 128 154 .south || decide (bonus 128 p ≤ bonus 154 p)) = true :=
  check_of_implication _ _ (bound482 p)
theorem guard483 (p : Pattern) (guard : pushGuard support p 128 154 180 180 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound483 (p : Pattern) (guard : pushGuard support p 128 154 180 180 = true) : bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder 180 - Generated.soko3_2Potential.boulder 154 + bonus 154 (change p 154 (some 180)) := by
  have certified := compare37 p (guard483 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 154 (some 180))
  have normalized := agree0 _ _ (change_representative support p 154 (some 180) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check483 (p : Pattern) : (!pushGuard support p 128 154 180 180 || decide (bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder 180 - Generated.soko3_2Potential.boulder 154 + bonus 154 (change p 154 (some 180)))) = true :=
  check_of_implication _ _ (bound483 p)
theorem guard484 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 127 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound484 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 127 .west = true) : bonus 128 p ≤ bonus 127 p := by
  have certified := compare103 p (guard484 p guard)
  simpa only [at128, at127, Int.zero_add] using certified
theorem check484 (p : Pattern) : (!walkGuard soko3_2.board support p 128 127 .west || decide (bonus 128 p ≤ bonus 127 p)) = true :=
  check_of_implication _ _ (bound484 p)
theorem guard485 (p : Pattern) (guard : pushGuard support p 128 127 126 126 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound485 (p : Pattern) (guard : pushGuard support p 128 127 126 126 = true) : bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some 126)) := by
  have certified := compare37 p (guard485 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 127 (some 126))
  have normalized := agree0 _ _ (change_representative support p 127 (some 126) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check485 (p : Pattern) : (!pushGuard support p 128 127 126 126 || decide (bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some 126)))) = true :=
  check_of_implication _ _ (bound485 p)
theorem guard486 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 101 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound486 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 101 .northWest = true) : bonus 128 p ≤ bonus 101 p := by
  have certified := compare103 p (guard486 p guard)
  simpa only [at128, at101, Int.zero_add] using certified
theorem check486 (p : Pattern) : (!walkGuard soko3_2.board support p 128 101 .northWest || decide (bonus 128 p ≤ bonus 101 p)) = true :=
  check_of_implication _ _ (bound486 p)
theorem guard487 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 153 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound487 (p : Pattern) (guard : walkGuard soko3_2.board support p 128 153 .southWest = true) : bonus 128 p ≤ bonus 153 p := by
  have certified := compare103 p (guard487 p guard)
  simpa only [at128, at153, Int.zero_add] using certified
theorem check487 (p : Pattern) : (!walkGuard soko3_2.board support p 128 153 .southWest || decide (bonus 128 p ≤ bonus 153 p)) = true :=
  check_of_implication _ _ (bound487 p)
theorem guard488 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 105 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound488 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 105 .north = true) : bonus 131 p ≤ bonus 105 p := by
  have certified := compare0 p (guard488 p guard)
  simpa only [at131, at105, Int.zero_add] using certified
theorem check488 (p : Pattern) : (!walkGuard soko3_2.board support p 131 105 .north || decide (bonus 131 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound488 p)
theorem guard489 (p : Pattern) (guard : pushGuard support p 131 105 79 79 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound489 (p : Pattern) (guard : pushGuard support p 131 105 79 79 = true) : bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder 79 - Generated.soko3_2Potential.boulder 105 + bonus 105 (change p 105 (some 79)) := by
  have certified := compare104 p (guard489 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 105 (some 79))
  have normalized := agree134 _ _ (change_representative support p 105 (some 79) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check489 (p : Pattern) : (!pushGuard support p 131 105 79 79 || decide (bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder 79 - Generated.soko3_2Potential.boulder 105 + bonus 105 (change p 105 (some 79)))) = true :=
  check_of_implication _ _ (bound489 p)
theorem guard490 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 157 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound490 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 157 .south = true) : bonus 131 p ≤ bonus 157 p := by
  have certified := compare0 p (guard490 p guard)
  simpa only [at131, at157, Int.zero_add] using certified
theorem check490 (p : Pattern) : (!walkGuard soko3_2.board support p 131 157 .south || decide (bonus 131 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound490 p)
theorem guard491 (p : Pattern) (guard : pushGuard support p 131 157 183 183 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound491 (p : Pattern) (guard : pushGuard support p 131 157 183 183 = true) : bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder 183 - Generated.soko3_2Potential.boulder 157 + bonus 157 (change p 157 (some 183)) := by
  have certified := compare104 p (guard491 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 157 (some 183))
  have normalized := agree134 _ _ (change_representative support p 157 (some 183) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check491 (p : Pattern) : (!pushGuard support p 131 157 183 183 || decide (bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder 183 - Generated.soko3_2Potential.boulder 157 + bonus 157 (change p 157 (some 183)))) = true :=
  check_of_implication _ _ (bound491 p)
theorem guard492 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 132 .east = true) : d841 p = 1 := by
  change (!false && !(p 132) && !false) = true at guard
  cases h132 : p 132
  all_goals simp [d0, d1, d841, h132] at guard ⊢
theorem bound492 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 132 .east = true) : bonus 131 p ≤ bonus 132 p := by
  have certified := compare612 p (guard492 p guard)
  simpa only [at131, at132, Int.zero_add] using certified
theorem check492 (p : Pattern) : (!walkGuard soko3_2.board support p 131 132 .east || decide (bonus 131 p ≤ bonus 132 p)) = true :=
  check_of_implication _ _ (bound492 p)
theorem guard493 (p : Pattern) (guard : pushGuard support p 131 132 133 133 = true) : d1132 p = 1 := by
  change (!false && (!true || (p 132)) && !(p 133) && (!(p 133) || false)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d910, d1132, h132, h133] at guard ⊢
theorem bound493 (p : Pattern) (guard : pushGuard support p 131 132 133 133 = true) : bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder 133 - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some 133)) := by
  have certified := compare2346 p (guard493 p guard)
  change d134 p ≤ (0 : Int) + d292 (change p 132 (some 133))
  have normalized := agree292 _ _ (change_representative support p 132 (some 133) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d292 (change p 132 (some 133))
  rw [sub1527]
  exact certified
theorem check493 (p : Pattern) : (!pushGuard support p 131 132 133 133 || decide (bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder 133 - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some 133)))) = true :=
  check_of_implication _ _ (bound493 p)
theorem guard494 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 106 .northEast = true) : d829 p = 1 := by
  change (!false && !(p 106) && !(true && false && (p 132))) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132
  all_goals simp [d0, d1, d829, h106, h132] at guard ⊢
theorem bound494 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 106 .northEast = true) : bonus 131 p ≤ bonus 106 p := by
  have certified := compare297 p (guard494 p guard)
  simpa only [at131, at106, Int.zero_add] using certified
theorem check494 (p : Pattern) : (!walkGuard soko3_2.board support p 131 106 .northEast || decide (bonus 131 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound494 p)
theorem guard495 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 158 .southEast = true) : d873 p = 1 := by
  change (!false && !(p 158) && !(true && false && (p 132))) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d873, h132, h158] at guard ⊢
theorem bound495 (p : Pattern) (guard : walkGuard soko3_2.board support p 131 158 .southEast = true) : bonus 131 p ≤ bonus 158 p := by
  have certified := compare2491 p (guard495 p guard)
  simpa only [at131, at158, Int.zero_add] using certified
theorem check495 (p : Pattern) : (!walkGuard soko3_2.board support p 131 158 .southEast || decide (bonus 131 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound495 p)
theorem guard496 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 106 .north = true) : d870 p = 1 := by
  change (!(p 132) && !(p 106) && !false) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132
  all_goals simp [d0, d1, d841, d870, h106, h132] at guard ⊢
theorem bound496 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 106 .north = true) : bonus 132 p ≤ bonus 106 p := by
  have certified := compare2533 p (guard496 p guard)
  simpa only [at132, at106, Int.zero_add] using certified
theorem check496 (p : Pattern) : (!walkGuard soko3_2.board support p 132 106 .north || decide (bonus 132 p ≤ bonus 106 p)) = true :=
  check_of_implication _ _ (bound496 p)
theorem guard497 (p : Pattern) (guard : pushGuard support p 132 106 80 80 = true) : d843 p = 1 := by
  change (!(p 132) && (!true || (p 106)) && !(p 80) && (!(p 80) || false)) = true at guard
  cases h80 : p 80 <;> cases h106 : p 106 <;> cases h132 : p 132
  all_goals simp [d0, d1, d841, d842, d843, h80, h106, h132] at guard ⊢
theorem bound497 (p : Pattern) (guard : pushGuard support p 132 106 80 80 = true) : bonus 132 p ≤ 1 + Generated.soko3_2Potential.boulder 80 - Generated.soko3_2Potential.boulder 106 + bonus 106 (change p 106 (some 80)) := by
  have certified := compare2560 p (guard497 p guard)
  change d292 p ≤ (1 : Int) + d183 (change p 106 (some 80))
  have normalized := agree183 _ _ (change_representative support p 106 (some 80) 10000 dummy_outside)
  rw [normalized]
  change d292 p ≤ (1 : Int) + d183 (change p 106 (some 80))
  rw [sub1629]
  exact certified
theorem check497 (p : Pattern) : (!pushGuard support p 132 106 80 80 || decide (bonus 132 p ≤ 1 + Generated.soko3_2Potential.boulder 80 - Generated.soko3_2Potential.boulder 106 + bonus 106 (change p 106 (some 80)))) = true :=
  check_of_implication _ _ (bound497 p)
theorem guard498 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 158 .south = true) : d1148 p = 1 := by
  change (!(p 132) && !(p 158) && !false) = true at guard
  cases h132 : p 132 <;> cases h158 : p 158
  all_goals simp [d0, d1, d873, d1148, h132, h158] at guard ⊢
theorem bound498 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 158 .south = true) : bonus 132 p ≤ bonus 158 p := by
  have certified := compare2631 p (guard498 p guard)
  simpa only [at132, at158, Int.zero_add] using certified
theorem check498 (p : Pattern) : (!walkGuard soko3_2.board support p 132 158 .south || decide (bonus 132 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound498 p)
theorem guard499 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 133 .east = true) : d912 p = 1 := by
  change (!(p 132) && !(p 133) && !false) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133
  all_goals simp [d0, d1, d910, d912, h132, h133] at guard ⊢
theorem bound499 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 133 .east = true) : bonus 132 p ≤ bonus 133 p := by
  have certified := compare2683 p (guard499 p guard)
  simpa only [at132, at133, Int.zero_add] using certified
theorem check499 (p : Pattern) : (!walkGuard soko3_2.board support p 132 133 .east || decide (bonus 132 p ≤ bonus 133 p)) = true :=
  check_of_implication _ _ (bound499 p)
theorem guard500 (p : Pattern) (guard : pushGuard support p 132 133 134 134 = true) : d1151 p = 1 := by
  change (!(p 132) && (!true || (p 133)) && !(p 134) && (!(p 134) || false)) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h134 : p 134
  all_goals simp [d0, d1, d915, d1150, d1151, h132, h133, h134] at guard ⊢
theorem bound500 (p : Pattern) (guard : pushGuard support p 132 133 134 134 = true) : bonus 132 p ≤ 1 + Generated.soko3_2Potential.boulder 134 - Generated.soko3_2Potential.boulder 133 + bonus 133 (change p 133 (some 134)) := by
  have certified := compare2746 p (guard500 p guard)
  change d292 p ≤ (0 : Int) + d327 (change p 133 (some 134))
  have normalized := agree327 _ _ (change_representative support p 133 (some 134) 10000 dummy_outside)
  rw [normalized]
  change d292 p ≤ (0 : Int) + d327 (change p 133 (some 134))
  rw [sub1686]
  exact certified
theorem check500 (p : Pattern) : (!pushGuard support p 132 133 134 134 || decide (bonus 132 p ≤ 1 + Generated.soko3_2Potential.boulder 134 - Generated.soko3_2Potential.boulder 133 + bonus 133 (change p 133 (some 134)))) = true :=
  check_of_implication _ _ (bound500 p)
theorem guard501 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 131 .west = true) : d841 p = 1 := by
  change (!(p 132) && !false && !false) = true at guard
  cases h132 : p 132
  all_goals simp [d0, d1, d841, h132] at guard ⊢
theorem bound501 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 131 .west = true) : bonus 132 p ≤ bonus 131 p := by
  have certified := compare2785 p (guard501 p guard)
  simpa only [at132, at131, Int.zero_add] using certified
theorem check501 (p : Pattern) : (!walkGuard soko3_2.board support p 132 131 .west || decide (bonus 132 p ≤ bonus 131 p)) = true :=
  check_of_implication _ _ (bound501 p)
theorem guard502 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 105 .northWest = true) : d841 p = 1 := by
  change (!(p 132) && !false && !(true && (p 106) && false)) = true at guard
  cases h106 : p 106 <;> cases h132 : p 132
  all_goals simp [d0, d1, d841, h106, h132] at guard ⊢
theorem bound502 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 105 .northWest = true) : bonus 132 p ≤ bonus 105 p := by
  have certified := compare2785 p (guard502 p guard)
  simpa only [at132, at105, Int.zero_add] using certified
theorem check502 (p : Pattern) : (!walkGuard soko3_2.board support p 132 105 .northWest || decide (bonus 132 p ≤ bonus 105 p)) = true :=
  check_of_implication _ _ (bound502 p)
theorem guard503 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 159 .southEast = true) : d1173 p = 1 := by
  change (!(p 132) && !(p 159) && !(true && (p 158) && (p 133))) = true at guard
  cases h132 : p 132 <;> cases h133 : p 133 <;> cases h158 : p 158 <;> cases h159 : p 159
  all_goals simp [d0, d1, d1167, d1171, d1172, d1173, h132, h133, h158, h159] at guard ⊢
theorem bound503 (p : Pattern) (guard : walkGuard soko3_2.board support p 132 159 .southEast = true) : bonus 132 p ≤ bonus 159 p := by
  have certified := compare2907 p (guard503 p guard)
  simpa only [at132, at159, Int.zero_add] using certified
theorem check503 (p : Pattern) : (!walkGuard soko3_2.board support p 132 159 .southEast || decide (bonus 132 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound503 p)
end NetHack.Sokoban32Refined
