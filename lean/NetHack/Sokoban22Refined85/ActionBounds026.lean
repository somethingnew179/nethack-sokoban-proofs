import NetHack.Sokoban22Refined85.ActionBounds025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard624 (p : Pattern) (guard : pushGuard support p 160 159 158 158 = true) : d4117 p = 1 := by
  change (!(p 160) && (!false || false) && !false && (!false || false)) = true at guard
  cases h160 : p 160
  all_goals simp [d0, d1, d4117, h160] at guard ⊢
theorem bound624 (p : Pattern) (guard : pushGuard support p 160 159 158 158 = true) : bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.boulder 159 + bonus 159 (change p 159 (some 158)) := by
  have certified := compare6398 p (guard624 p guard)
  change d789 p ≤ (2 : Int) + d267 (change p 159 (some 158))
  have normalized := agree267 _ _ (change_representative support p 159 (some 158) 10000 dummy_outside)
  rw [normalized]
  change d789 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check624 (p : Pattern) : (!pushGuard support p 160 159 158 158 || decide (bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.boulder 159 + bonus 159 (change p 159 (some 158)))) = true :=
  check_of_implication _ _ (bound624 p)
theorem guard625 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 181 .southWest = true) : d4117 p = 1 := by
  change (!(p 160) && !false && !(true && (p 182) && false)) = true at guard
  cases h160 : p 160 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4117, h160, h182] at guard ⊢
theorem bound625 (p : Pattern) (guard : walkGuard soko2_2.board support p 160 181 .southWest = true) : bonus 160 p ≤ bonus 181 p := by
  have certified := compare6274 p (guard625 p guard)
  simpa only [at160, at181, Int.zero_add] using certified
theorem check625 (p : Pattern) : (!walkGuard soko2_2.board support p 160 181 .southWest || decide (bonus 160 p ≤ bonus 181 p)) = true :=
  check_of_implication _ _ (bound625 p)
theorem guard626 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 162 .east = true) : d4670 p = 1 := by
  change (!(p 161) && !(p 162) && !false) = true at guard
  cases h161 : p 161 <;> cases h162 : p 162
  all_goals simp [d0, d1, d4395, d4670, h161, h162] at guard ⊢
theorem bound626 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 162 .east = true) : bonus 161 p ≤ bonus 162 p := by
  have certified := compare6671 p (guard626 p guard)
  simpa only [at161, at162, Int.zero_add] using certified
theorem check626 (p : Pattern) : (!walkGuard soko2_2.board support p 161 162 .east || decide (bonus 161 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound626 p)
theorem guard627 (p : Pattern) (guard : pushGuard support p 161 162 163 163 = true) : d4673 p = 1 := by
  change (!(p 161) && (!true || (p 162)) && !(p 163) && (!(p 163) || false)) = true at guard
  cases h161 : p 161 <;> cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4672, d4673, h161, h162, h163] at guard ⊢
theorem bound627 (p : Pattern) (guard : pushGuard support p 161 162 163 163 = true) : bonus 161 p ≤ 1 + Generated.soko2_2Potential.boulder 163 - Generated.soko2_2Potential.boulder 162 + bonus 162 (change p 162 (some 163)) := by
  have certified := compare6948 p (guard627 p guard)
  change d948 p ≤ (2 : Int) + d1150 (change p 162 (some 163))
  have normalized := agree1150 _ _ (change_representative support p 162 (some 163) 10000 dummy_outside)
  rw [normalized]
  change d948 p ≤ (2 : Int) + d1150 (change p 162 (some 163))
  rw [sub5421]
  exact certified
theorem check627 (p : Pattern) : (!pushGuard support p 161 162 163 163 || decide (bonus 161 p ≤ 1 + Generated.soko2_2Potential.boulder 163 - Generated.soko2_2Potential.boulder 162 + bonus 162 (change p 162 (some 163)))) = true :=
  check_of_implication _ _ (bound627 p)
theorem guard628 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 160 .west = true) : d4301 p = 1 := by
  change (!(p 161) && !(p 160) && !false) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d4299, d4301, h160, h161] at guard ⊢
theorem bound628 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 160 .west = true) : bonus 161 p ≤ bonus 160 p := by
  have certified := compare7119 p (guard628 p guard)
  simpa only [at161, at160, Int.zero_add] using certified
theorem check628 (p : Pattern) : (!walkGuard soko2_2.board support p 161 160 .west || decide (bonus 161 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound628 p)
theorem guard629 (p : Pattern) (guard : pushGuard support p 161 160 159 159 = true) : d4432 p = 1 := by
  change (!(p 161) && (!true || (p 160)) && !false && (!false || false)) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d4299, d4432, h160, h161] at guard ⊢
theorem bound629 (p : Pattern) (guard : pushGuard support p 161 160 159 159 = true) : bonus 161 p ≤ 1 + Generated.soko2_2Potential.boulder 159 - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some 159)) := by
  have certified := compare7303 p (guard629 p guard)
  change d948 p ≤ (2 : Int) + d789 (change p 160 (some 159))
  have normalized := agree789 _ _ (change_representative support p 160 (some 159) 10000 dummy_outside)
  rw [normalized]
  change d948 p ≤ (2 : Int) + d789 (change p 160 none)
  rw [sub5615]
  exact certified
theorem check629 (p : Pattern) : (!pushGuard support p 161 160 159 159 || decide (bonus 161 p ≤ 1 + Generated.soko2_2Potential.boulder 159 - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some 159)))) = true :=
  check_of_implication _ _ (bound629 p)
theorem guard630 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 138 .northWest = true) : d4302 p = 1 := by
  change (!(p 161) && !(p 138) && !(true && true && (p 160))) = true at guard
  cases h138 : p 138 <;> cases h160 : p 160 <;> cases h161 : p 161
  all_goals simp [d0, d1, d4299, d4301, d4302, h138, h160, h161] at guard ⊢
theorem bound630 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 138 .northWest = true) : bonus 161 p ≤ bonus 138 p := by
  have certified := compare7413 p (guard630 p guard)
  simpa only [at161, at138, Int.zero_add] using certified
theorem check630 (p : Pattern) : (!walkGuard soko2_2.board support p 161 138 .northWest || decide (bonus 161 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound630 p)
theorem guard631 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 184 .southEast = true) : d4670 p = 1 := by
  change (!(p 161) && !false && !(true && true && (p 162))) = true at guard
  cases h161 : p 161 <;> cases h162 : p 162
  all_goals simp [d0, d1, d4395, d4670, h161, h162] at guard ⊢
theorem bound631 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 184 .southEast = true) : bonus 161 p ≤ bonus 184 p := by
  have certified := compare7612 p (guard631 p guard)
  simpa only [at161, at184, Int.zero_add] using certified
theorem check631 (p : Pattern) : (!walkGuard soko2_2.board support p 161 184 .southEast || decide (bonus 161 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound631 p)
theorem guard632 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 182 .southWest = true) : d4764 p = 1 := by
  change (!(p 161) && !(p 182) && !(true && true && (p 160))) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4206, d4763, d4764, h160, h161, h182] at guard ⊢
theorem bound632 (p : Pattern) (guard : walkGuard soko2_2.board support p 161 182 .southWest = true) : bonus 161 p ≤ bonus 182 p := by
  have certified := compare7783 p (guard632 p guard)
  simpa only [at161, at182, Int.zero_add] using certified
theorem check632 (p : Pattern) : (!walkGuard soko2_2.board support p 161 182 .southWest || decide (bonus 161 p ≤ bonus 182 p)) = true :=
  check_of_implication _ _ (bound632 p)
theorem guard633 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 184 .south = true) : d4395 p = 1 := by
  change (!(p 162) && !false && !false) = true at guard
  cases h162 : p 162
  all_goals simp [d0, d1, d4395, h162] at guard ⊢
theorem bound633 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 184 .south = true) : bonus 162 p ≤ bonus 184 p := by
  have certified := compare8042 p (guard633 p guard)
  simpa only [at162, at184, Int.zero_add] using certified
theorem check633 (p : Pattern) : (!walkGuard soko2_2.board support p 162 184 .south || decide (bonus 162 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound633 p)
theorem guard634 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 163 .east = true) : d4397 p = 1 := by
  change (!(p 162) && !(p 163) && !false) = true at guard
  cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4397, h162, h163] at guard ⊢
theorem bound634 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 163 .east = true) : bonus 162 p ≤ bonus 163 p := by
  have certified := compare8363 p (guard634 p guard)
  simpa only [at162, at163, Int.zero_add] using certified
theorem check634 (p : Pattern) : (!walkGuard soko2_2.board support p 162 163 .east || decide (bonus 162 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound634 p)
theorem guard635 (p : Pattern) (guard : pushGuard support p 162 163 164 164 = true) : d4765 p = 1 := by
  change (!(p 162) && (!true || (p 163)) && !false && (!false || false)) = true at guard
  cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4147, d4765, h162, h163] at guard ⊢
theorem bound635 (p : Pattern) (guard : pushGuard support p 162 163 164 164 = true) : bonus 162 p ≤ 1 + Generated.soko2_2Potential.boulder 164 - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some 164)) := by
  have certified := compare8667 p (guard635 p guard)
  change d1150 p ≤ (4 : Int) + d1398 (change p 163 (some 164))
  have normalized := agree1398 _ _ (change_representative support p 163 (some 164) 10000 dummy_outside)
  rw [normalized]
  change d1150 p ≤ (4 : Int) + d1398 (change p 163 none)
  rw [sub4017]
  exact certified
theorem check635 (p : Pattern) : (!pushGuard support p 162 163 164 164 || decide (bonus 162 p ≤ 1 + Generated.soko2_2Potential.boulder 164 - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some 164)))) = true :=
  check_of_implication _ _ (bound635 p)
theorem guard636 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 161 .west = true) : d4670 p = 1 := by
  change (!(p 162) && !(p 161) && !false) = true at guard
  cases h161 : p 161 <;> cases h162 : p 162
  all_goals simp [d0, d1, d4395, d4670, h161, h162] at guard ⊢
theorem bound636 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 161 .west = true) : bonus 162 p ≤ bonus 161 p := by
  have certified := compare8912 p (guard636 p guard)
  simpa only [at162, at161, Int.zero_add] using certified
theorem check636 (p : Pattern) : (!walkGuard soko2_2.board support p 162 161 .west || decide (bonus 162 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound636 p)
theorem guard637 (p : Pattern) (guard : pushGuard support p 162 161 160 160 = true) : d4618 p = 1 := by
  change (!(p 162) && (!true || (p 161)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161 <;> cases h162 : p 162
  all_goals simp [d0, d1, d4395, d4617, d4618, h160, h161, h162] at guard ⊢
theorem bound637 (p : Pattern) (guard : pushGuard support p 162 161 160 160 = true) : bonus 162 p ≤ 1 + Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.boulder 161 + bonus 161 (change p 161 (some 160)) := by
  have certified := compare9128 p (guard637 p guard)
  change d1150 p ≤ (0 : Int) + d948 (change p 161 (some 160))
  have normalized := agree948 _ _ (change_representative support p 161 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d1150 p ≤ (0 : Int) + d948 (change p 161 (some 160))
  rw [sub5818]
  exact certified
theorem check637 (p : Pattern) : (!pushGuard support p 162 161 160 160 || decide (bonus 162 p ≤ 1 + Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.boulder 161 + bonus 161 (change p 161 (some 160)))) = true :=
  check_of_implication _ _ (bound637 p)
theorem guard638 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 141 .northEast = true) : d4398 p = 1 := by
  change (!(p 162) && !(p 141) && !(true && true && (p 163))) = true at guard
  cases h141 : p 141 <;> cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4397, d4398, h141, h162, h163] at guard ⊢
theorem bound638 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 141 .northEast = true) : bonus 162 p ≤ bonus 141 p := by
  have certified := compare9317 p (guard638 p guard)
  simpa only [at162, at141, Int.zero_add] using certified
theorem check638 (p : Pattern) : (!walkGuard soko2_2.board support p 162 141 .northEast || decide (bonus 162 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound638 p)
theorem guard639 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 185 .southEast = true) : d4395 p = 1 := by
  change (!(p 162) && !false && !(true && false && (p 163))) = true at guard
  cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4395, h162, h163] at guard ⊢
theorem bound639 (p : Pattern) (guard : walkGuard soko2_2.board support p 162 185 .southEast = true) : bonus 162 p ≤ bonus 185 p := by
  have certified := compare8042 p (guard639 p guard)
  simpa only [at162, at185, Int.zero_add] using certified
theorem check639 (p : Pattern) : (!walkGuard soko2_2.board support p 162 185 .southEast || decide (bonus 162 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound639 p)
theorem guard640 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 141 .north = true) : d4303 p = 1 := by
  change (!(p 163) && !(p 141) && !false) = true at guard
  cases h141 : p 141 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4303, h141, h163] at guard ⊢
theorem bound640 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 141 .north = true) : bonus 163 p ≤ bonus 141 p := by
  have certified := compare9557 p (guard640 p guard)
  simpa only [at163, at141, Int.zero_add] using certified
theorem check640 (p : Pattern) : (!walkGuard soko2_2.board support p 163 141 .north || decide (bonus 163 p ≤ bonus 141 p)) = true :=
  check_of_implication _ _ (bound640 p)
theorem guard641 (p : Pattern) (guard : pushGuard support p 163 141 119 119 = true) : d4149 p = 1 := by
  change (!(p 163) && (!true || (p 141)) && !false && (!false || false)) = true at guard
  cases h141 : p 141 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4149, h141, h163] at guard ⊢
theorem bound641 (p : Pattern) (guard : pushGuard support p 163 141 119 119 = true) : bonus 163 p ≤ 1 + Generated.soko2_2Potential.boulder 119 - Generated.soko2_2Potential.boulder 141 + bonus 141 (change p 141 (some 119)) := by
  have certified := compare9797 p (guard641 p guard)
  change d1398 p ≤ (2 : Int) + d709 (change p 141 (some 119))
  have normalized := agree709 _ _ (change_representative support p 141 (some 119) 10000 dummy_outside)
  rw [normalized]
  change d1398 p ≤ (2 : Int) + d709 (change p 141 none)
  rw [sub6007]
  exact certified
theorem check641 (p : Pattern) : (!pushGuard support p 163 141 119 119 || decide (bonus 163 p ≤ 1 + Generated.soko2_2Potential.boulder 119 - Generated.soko2_2Potential.boulder 141 + bonus 141 (change p 141 (some 119)))) = true :=
  check_of_implication _ _ (bound641 p)
theorem guard642 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 185 .south = true) : d4148 p = 1 := by
  change (!(p 163) && !false && !false) = true at guard
  cases h163 : p 163
  all_goals simp [d0, d1, d4148, h163] at guard ⊢
theorem bound642 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 185 .south = true) : bonus 163 p ≤ bonus 185 p := by
  have certified := compare10079 p (guard642 p guard)
  simpa only [at163, at185, Int.zero_add] using certified
theorem check642 (p : Pattern) : (!walkGuard soko2_2.board support p 163 185 .south || decide (bonus 163 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound642 p)
theorem guard643 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 164 .east = true) : d4148 p = 1 := by
  change (!(p 163) && !false && !false) = true at guard
  cases h163 : p 163
  all_goals simp [d0, d1, d4148, h163] at guard ⊢
theorem bound643 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 164 .east = true) : bonus 163 p ≤ bonus 164 p := by
  have certified := compare10079 p (guard643 p guard)
  simpa only [at163, at164, Int.zero_add] using certified
theorem check643 (p : Pattern) : (!walkGuard soko2_2.board support p 163 164 .east || decide (bonus 163 p ≤ bonus 164 p)) = true :=
  check_of_implication _ _ (bound643 p)
theorem guard644 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 162 .west = true) : d4397 p = 1 := by
  change (!(p 163) && !(p 162) && !false) = true at guard
  cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4397, h162, h163] at guard ⊢
theorem bound644 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 162 .west = true) : bonus 163 p ≤ bonus 162 p := by
  have certified := compare10341 p (guard644 p guard)
  simpa only [at163, at162, Int.zero_add] using certified
theorem check644 (p : Pattern) : (!walkGuard soko2_2.board support p 163 162 .west || decide (bonus 163 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound644 p)
theorem guard645 (p : Pattern) (guard : pushGuard support p 163 162 161 161 = true) : d4673 p = 1 := by
  change (!(p 163) && (!true || (p 162)) && !(p 161) && (!(p 161) || false)) = true at guard
  cases h161 : p 161 <;> cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, d4672, d4673, h161, h162, h163] at guard ⊢
theorem bound645 (p : Pattern) (guard : pushGuard support p 163 162 161 161 = true) : bonus 163 p ≤ 1 + Generated.soko2_2Potential.boulder 161 - Generated.soko2_2Potential.boulder 162 + bonus 162 (change p 162 (some 161)) := by
  have certified := compare10635 p (guard645 p guard)
  change d1398 p ≤ (0 : Int) + d1150 (change p 162 (some 161))
  have normalized := agree1150 _ _ (change_representative support p 162 (some 161) 10000 dummy_outside)
  rw [normalized]
  change d1398 p ≤ (0 : Int) + d1150 (change p 162 (some 161))
  rw [sub6259]
  exact certified
theorem check645 (p : Pattern) : (!pushGuard support p 163 162 161 161 || decide (bonus 163 p ≤ 1 + Generated.soko2_2Potential.boulder 161 - Generated.soko2_2Potential.boulder 162 + bonus 162 (change p 162 (some 161)))) = true :=
  check_of_implication _ _ (bound645 p)
theorem guard646 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 186 .southEast = true) : d4148 p = 1 := by
  change (!(p 163) && !false && !(true && false && false)) = true at guard
  cases h163 : p 163
  all_goals simp [d0, d1, d4148, h163] at guard ⊢
theorem bound646 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 186 .southEast = true) : bonus 163 p ≤ bonus 186 p := by
  have certified := compare10079 p (guard646 p guard)
  simpa only [at163, at186, Int.zero_add] using certified
theorem check646 (p : Pattern) : (!walkGuard soko2_2.board support p 163 186 .southEast || decide (bonus 163 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound646 p)
theorem guard647 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 184 .southWest = true) : d4148 p = 1 := by
  change (!(p 163) && !false && !(true && false && (p 162))) = true at guard
  cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, h162, h163] at guard ⊢
theorem bound647 (p : Pattern) (guard : walkGuard soko2_2.board support p 163 184 .southWest = true) : bonus 163 p ≤ bonus 184 p := by
  have certified := compare10079 p (guard647 p guard)
  simpa only [at163, at184, Int.zero_add] using certified
theorem check647 (p : Pattern) : (!walkGuard soko2_2.board support p 163 184 .southWest || decide (bonus 163 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound647 p)
end NetHack.Sokoban22Refined85
