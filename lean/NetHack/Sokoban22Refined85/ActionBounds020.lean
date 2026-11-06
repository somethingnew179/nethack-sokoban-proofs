import NetHack.Sokoban22Refined85.ActionBounds019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard480 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 135 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound480 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 135 .west = true) : bonus 136 p ≤ bonus 135 p := by
  have certified := compare0 p (guard480 p guard)
  simpa only [at136, at135, Int.zero_add] using certified
theorem check480 (p : Pattern) : (!walkGuard soko2_2.board support p 136 135 .west || decide (bonus 136 p ≤ bonus 135 p)) = true :=
  check_of_implication _ _ (bound480 p)
theorem guard481 (p : Pattern) (guard : pushGuard support p 136 135 134 134 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound481 (p : Pattern) (guard : pushGuard support p 136 135 134 134 = true) : bonus 136 p ≤ 1 + Generated.soko2_2Potential.boulder 134 - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some 134)) := by
  have certified := compare2458 p (guard481 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 135 (some 134))
  have normalized := agree267 _ _ (change_representative support p 135 (some 134) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check481 (p : Pattern) : (!pushGuard support p 136 135 134 134 || decide (bonus 136 p ≤ 1 + Generated.soko2_2Potential.boulder 134 - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some 134)))) = true :=
  check_of_implication _ _ (bound481 p)
theorem guard482 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 115 .northEast = true) : d4058 p = 1 := by
  change (!false && !(p 115) && !(true && false && true)) = true at guard
  cases h115 : p 115
  all_goals simp [d0, d1, d4058, h115] at guard ⊢
theorem bound482 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 115 .northEast = true) : bonus 136 p ≤ bonus 115 p := by
  have certified := compare1485 p (guard482 p guard)
  simpa only [at136, at115, Int.zero_add] using certified
theorem check482 (p : Pattern) : (!walkGuard soko2_2.board support p 136 115 .northEast || decide (bonus 136 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound482 p)
theorem guard483 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 113 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound483 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 113 .northWest = true) : bonus 136 p ≤ bonus 113 p := by
  have certified := compare0 p (guard483 p guard)
  simpa only [at136, at113, Int.zero_add] using certified
theorem check483 (p : Pattern) : (!walkGuard soko2_2.board support p 136 113 .northWest || decide (bonus 136 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound483 p)
theorem guard484 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 159 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound484 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 159 .southEast = true) : bonus 136 p ≤ bonus 159 p := by
  have certified := compare0 p (guard484 p guard)
  simpa only [at136, at159, Int.zero_add] using certified
theorem check484 (p : Pattern) : (!walkGuard soko2_2.board support p 136 159 .southEast || decide (bonus 136 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound484 p)
theorem guard485 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 157 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound485 (p : Pattern) (guard : walkGuard soko2_2.board support p 136 157 .southWest = true) : bonus 136 p ≤ bonus 157 p := by
  have certified := compare0 p (guard485 p guard)
  simpa only [at136, at157, Int.zero_add] using certified
theorem check485 (p : Pattern) : (!walkGuard soko2_2.board support p 136 157 .southWest || decide (bonus 136 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound485 p)
theorem guard486 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 116 .north = true) : d4113 p = 1 := by
  change (!(p 138) && !(p 116) && !false) = true at guard
  cases h116 : p 116 <;> cases h138 : p 138
  all_goals simp [d0, d1, d4068, d4113, h116, h138] at guard ⊢
theorem bound486 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 116 .north = true) : bonus 138 p ≤ bonus 116 p := by
  have certified := compare2504 p (guard486 p guard)
  simpa only [at138, at116, Int.zero_add] using certified
theorem check486 (p : Pattern) : (!walkGuard soko2_2.board support p 138 116 .north || decide (bonus 138 p ≤ bonus 116 p)) = true :=
  check_of_implication _ _ (bound486 p)
theorem guard487 (p : Pattern) (guard : pushGuard support p 138 116 94 94 = true) : d4069 p = 1 := by
  change (!(p 138) && (!true || (p 116)) && !false && (!false || false)) = true at guard
  cases h116 : p 116 <;> cases h138 : p 138
  all_goals simp [d0, d1, d4068, d4069, h116, h138] at guard ⊢
theorem bound487 (p : Pattern) (guard : pushGuard support p 138 116 94 94 = true) : bonus 138 p ≤ 1 + Generated.soko2_2Potential.boulder 94 - Generated.soko2_2Potential.boulder 116 + bonus 116 (change p 116 (some 94)) := by
  have certified := compare2782 p (guard487 p guard)
  change d652 p ≤ (4 : Int) + d516 (change p 116 (some 94))
  have normalized := agree516 _ _ (change_representative support p 116 (some 94) 10000 dummy_outside)
  rw [normalized]
  change d652 p ≤ (4 : Int) + d516 (change p 116 none)
  rw [sub3496]
  exact certified
theorem check487 (p : Pattern) : (!pushGuard support p 138 116 94 94 || decide (bonus 138 p ≤ 1 + Generated.soko2_2Potential.boulder 94 - Generated.soko2_2Potential.boulder 116 + bonus 116 (change p 116 (some 94)))) = true :=
  check_of_implication _ _ (bound487 p)
theorem guard488 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 160 .south = true) : d4203 p = 1 := by
  change (!(p 138) && !(p 160) && !false) = true at guard
  cases h138 : p 138 <;> cases h160 : p 160
  all_goals simp [d0, d1, d4117, d4203, h138, h160] at guard ⊢
theorem bound488 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 160 .south = true) : bonus 138 p ≤ bonus 160 p := by
  have certified := compare2906 p (guard488 p guard)
  simpa only [at138, at160, Int.zero_add] using certified
theorem check488 (p : Pattern) : (!walkGuard soko2_2.board support p 138 160 .south || decide (bonus 138 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound488 p)
theorem guard489 (p : Pattern) (guard : pushGuard support p 138 160 182 182 = true) : d4208 p = 1 := by
  change (!(p 138) && (!true || (p 160)) && !(p 182) && (!(p 182) || false)) = true at guard
  cases h138 : p 138 <;> cases h160 : p 160 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4206, d4207, d4208, h138, h160, h182] at guard ⊢
theorem bound489 (p : Pattern) (guard : pushGuard support p 138 160 182 182 = true) : bonus 138 p ≤ 1 + Generated.soko2_2Potential.boulder 182 - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some 182)) := by
  have certified := compare3173 p (guard489 p guard)
  change d652 p ≤ (0 : Int) + d789 (change p 160 (some 182))
  have normalized := agree789 _ _ (change_representative support p 160 (some 182) 10000 dummy_outside)
  rw [normalized]
  change d652 p ≤ (0 : Int) + d789 (change p 160 (some 182))
  rw [sub3690]
  exact certified
theorem check489 (p : Pattern) : (!pushGuard support p 138 160 182 182 || decide (bonus 138 p ≤ 1 + Generated.soko2_2Potential.boulder 182 - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some 182)))) = true :=
  check_of_implication _ _ (bound489 p)
theorem guard490 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 115 .northWest = true) : d4114 p = 1 := by
  change (!(p 138) && !(p 115) && !(true && (p 116) && true)) = true at guard
  cases h115 : p 115 <;> cases h116 : p 116 <;> cases h138 : p 138
  all_goals simp [d0, d1, d4068, d4113, d4114, h115, h116, h138] at guard ⊢
theorem bound490 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 115 .northWest = true) : bonus 138 p ≤ bonus 115 p := by
  have certified := compare3198 p (guard490 p guard)
  simpa only [at138, at115, Int.zero_add] using certified
theorem check490 (p : Pattern) : (!walkGuard soko2_2.board support p 138 115 .northWest || decide (bonus 138 p ≤ bonus 115 p)) = true :=
  check_of_implication _ _ (bound490 p)
theorem guard491 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 161 .southEast = true) : d4302 p = 1 := by
  change (!(p 138) && !(p 161) && !(true && (p 160) && true)) = true at guard
  cases h138 : p 138 <;> cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d4299, d4301, d4302, h138, h160, h161] at guard ⊢
theorem bound491 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 161 .southEast = true) : bonus 138 p ≤ bonus 161 p := by
  have certified := compare3365 p (guard491 p guard)
  simpa only [at138, at161, Int.zero_add] using certified
theorem check491 (p : Pattern) : (!walkGuard soko2_2.board support p 138 161 .southEast || decide (bonus 138 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound491 p)
theorem guard492 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 159 .southWest = true) : d4203 p = 1 := by
  change (!(p 138) && !false && !(true && (p 160) && true)) = true at guard
  cases h138 : p 138 <;> cases h160 : p 160
  all_goals simp [d0, d1, d4117, d4203, h138, h160] at guard ⊢
theorem bound492 (p : Pattern) (guard : walkGuard soko2_2.board support p 138 159 .southWest = true) : bonus 138 p ≤ bonus 159 p := by
  have certified := compare3443 p (guard492 p guard)
  simpa only [at138, at159, Int.zero_add] using certified
theorem check492 (p : Pattern) : (!walkGuard soko2_2.board support p 138 159 .southWest || decide (bonus 138 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound492 p)
theorem guard493 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 119 .north = true) : d4077 p = 1 := by
  change (!(p 141) && !false && !false) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d4077, h141] at guard ⊢
theorem bound493 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 119 .north = true) : bonus 141 p ≤ bonus 119 p := by
  have certified := compare3523 p (guard493 p guard)
  simpa only [at141, at119, Int.zero_add] using certified
theorem check493 (p : Pattern) : (!walkGuard soko2_2.board support p 141 119 .north || decide (bonus 141 p ≤ bonus 119 p)) = true :=
  check_of_implication _ _ (bound493 p)
theorem guard494 (p : Pattern) (guard : pushGuard support p 141 119 97 97 = true) : d4077 p = 1 := by
  change (!(p 141) && (!false || false) && !false && (!false || false)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d4077, h141] at guard ⊢
theorem bound494 (p : Pattern) (guard : pushGuard support p 141 119 97 97 = true) : bonus 141 p ≤ 1 + Generated.soko2_2Potential.boulder 97 - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some 97)) := by
  have certified := compare3612 p (guard494 p guard)
  change d709 p ≤ (2 : Int) + d312 (change p 119 (some 97))
  have normalized := agree312 _ _ (change_representative support p 119 (some 97) 10000 dummy_outside)
  rw [normalized]
  change d709 p ≤ (2 : Int) + d312 (change p 10000 none)
  rw [sub412]
  exact certified
theorem check494 (p : Pattern) : (!pushGuard support p 141 119 97 97 || decide (bonus 141 p ≤ 1 + Generated.soko2_2Potential.boulder 97 - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some 97)))) = true :=
  check_of_implication _ _ (bound494 p)
theorem guard495 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 163 .south = true) : d4303 p = 1 := by
  change (!(p 141) && !(p 163) && !false) = true at guard
  cases h141 : p 141 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4303, h141, h163] at guard ⊢
theorem bound495 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 163 .south = true) : bonus 141 p ≤ bonus 163 p := by
  have certified := compare3876 p (guard495 p guard)
  simpa only [at141, at163, Int.zero_add] using certified
theorem check495 (p : Pattern) : (!walkGuard soko2_2.board support p 141 163 .south || decide (bonus 141 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound495 p)
theorem guard496 (p : Pattern) (guard : pushGuard support p 141 163 185 185 = true) : d4304 p = 1 := by
  change (!(p 141) && (!true || (p 163)) && !false && (!false || false)) = true at guard
  cases h141 : p 141 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4147, d4304, h141, h163] at guard ⊢
theorem bound496 (p : Pattern) (guard : pushGuard support p 141 163 185 185 = true) : bonus 141 p ≤ 1 + Generated.soko2_2Potential.boulder 185 - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some 185)) := by
  have certified := compare4061 p (guard496 p guard)
  change d709 p ≤ (4 : Int) + d1398 (change p 163 (some 185))
  have normalized := agree1398 _ _ (change_representative support p 163 (some 185) 10000 dummy_outside)
  rw [normalized]
  change d709 p ≤ (4 : Int) + d1398 (change p 163 none)
  rw [sub4017]
  exact certified
theorem check496 (p : Pattern) : (!pushGuard support p 141 163 185 185 || decide (bonus 141 p ≤ 1 + Generated.soko2_2Potential.boulder 185 - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some 185)))) = true :=
  check_of_implication _ _ (bound496 p)
theorem guard497 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 120 .northEast = true) : d4077 p = 1 := by
  change (!(p 141) && !false && !(true && false && true)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d4077, h141] at guard ⊢
theorem bound497 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 120 .northEast = true) : bonus 141 p ≤ bonus 120 p := by
  have certified := compare3523 p (guard497 p guard)
  simpa only [at141, at120, Int.zero_add] using certified
theorem check497 (p : Pattern) : (!walkGuard soko2_2.board support p 141 120 .northEast || decide (bonus 141 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound497 p)
theorem guard498 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 118 .northWest = true) : d4077 p = 1 := by
  change (!(p 141) && !false && !(true && false && true)) = true at guard
  cases h141 : p 141
  all_goals simp [d0, d1, d4077, h141] at guard ⊢
theorem bound498 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 118 .northWest = true) : bonus 141 p ≤ bonus 118 p := by
  have certified := compare3523 p (guard498 p guard)
  simpa only [at141, at118, Int.zero_add] using certified
theorem check498 (p : Pattern) : (!walkGuard soko2_2.board support p 141 118 .northWest || decide (bonus 141 p ≤ bonus 118 p)) = true :=
  check_of_implication _ _ (bound498 p)
theorem guard499 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 164 .southEast = true) : d4303 p = 1 := by
  change (!(p 141) && !false && !(true && (p 163) && true)) = true at guard
  cases h141 : p 141 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4303, h141, h163] at guard ⊢
theorem bound499 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 164 .southEast = true) : bonus 141 p ≤ bonus 164 p := by
  have certified := compare4211 p (guard499 p guard)
  simpa only [at141, at164, Int.zero_add] using certified
theorem check499 (p : Pattern) : (!walkGuard soko2_2.board support p 141 164 .southEast || decide (bonus 141 p ≤ bonus 164 p)) = true :=
  check_of_implication _ _ (bound499 p)
theorem guard500 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 162 .southWest = true) : d4398 p = 1 := by
  change (!(p 141) && !(p 162) && !(true && (p 163) && true)) = true at guard
  cases h141 : p 141 <;> cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4397, d4398, h141, h162, h163] at guard ⊢
theorem bound500 (p : Pattern) (guard : walkGuard soko2_2.board support p 141 162 .southWest = true) : bonus 141 p ≤ bonus 162 p := by
  have certified := compare4415 p (guard500 p guard)
  simpa only [at141, at162, Int.zero_add] using certified
theorem check500 (p : Pattern) : (!walkGuard soko2_2.board support p 141 162 .southWest || decide (bonus 141 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound500 p)
theorem guard501 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 122 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound501 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 122 .north = true) : bonus 144 p ≤ bonus 122 p := by
  have certified := compare1086 p (guard501 p guard)
  simpa only [at144, at122, Int.zero_add] using certified
theorem check501 (p : Pattern) : (!walkGuard soko2_2.board support p 144 122 .north || decide (bonus 144 p ≤ bonus 122 p)) = true :=
  check_of_implication _ _ (bound501 p)
theorem guard502 (p : Pattern) (guard : pushGuard support p 144 122 100 100 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound502 (p : Pattern) (guard : pushGuard support p 144 122 100 100 = true) : bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder 100 - Generated.soko2_2Potential.boulder 122 + bonus 122 (change p 122 (some 100)) := by
  have certified := compare1087 p (guard502 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 122 (some 100))
  have normalized := agree0 _ _ (change_representative support p 122 (some 100) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check502 (p : Pattern) : (!pushGuard support p 144 122 100 100 || decide (bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder 100 - Generated.soko2_2Potential.boulder 122 + bonus 122 (change p 122 (some 100)))) = true :=
  check_of_implication _ _ (bound502 p)
theorem guard503 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 166 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound503 (p : Pattern) (guard : walkGuard soko2_2.board support p 144 166 .south = true) : bonus 144 p ≤ bonus 166 p := by
  have certified := compare1086 p (guard503 p guard)
  simpa only [at144, at166, Int.zero_add] using certified
theorem check503 (p : Pattern) : (!walkGuard soko2_2.board support p 144 166 .south || decide (bonus 144 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound503 p)
end NetHack.Sokoban22Refined85
