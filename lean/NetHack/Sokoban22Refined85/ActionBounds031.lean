import NetHack.Sokoban22Refined85.ActionBounds030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard744 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 160 .northEast = true) : d4117 p = 1 := by
  change (!false && !(p 160) && !(true && false && (p 182))) = true at guard
  cases h160 : p 160 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4117, h160, h182] at guard ⊢
theorem bound744 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 160 .northEast = true) : bonus 181 p ≤ bonus 160 p := by
  have certified := compare4686 p (guard744 p guard)
  simpa only [at181, at160, Int.zero_add] using certified
theorem check744 (p : Pattern) : (!walkGuard soko2_2.board support p 181 160 .northEast || decide (bonus 181 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound744 p)
theorem guard745 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 158 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound745 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 158 .northWest = true) : bonus 181 p ≤ bonus 158 p := by
  have certified := compare0 p (guard745 p guard)
  simpa only [at181, at158, Int.zero_add] using certified
theorem check745 (p : Pattern) : (!walkGuard soko2_2.board support p 181 158 .northWest || decide (bonus 181 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound745 p)
theorem guard746 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 204 .southEast = true) : d4967 p = 1 := by
  change (!false && !(p 204) && !(true && true && (p 182))) = true at guard
  cases h182 : p 182 <;> cases h204 : p 204
  all_goals simp [d0, d1, d4474, d4967, h182, h204] at guard ⊢
theorem bound746 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 204 .southEast = true) : bonus 181 p ≤ bonus 204 p := by
  have certified := compare11857 p (guard746 p guard)
  simpa only [at181, at204, Int.zero_add] using certified
theorem check746 (p : Pattern) : (!walkGuard soko2_2.board support p 181 204 .southEast || decide (bonus 181 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound746 p)
theorem guard747 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 202 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound747 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 202 .southWest = true) : bonus 181 p ≤ bonus 202 p := by
  have certified := compare0 p (guard747 p guard)
  simpa only [at181, at202, Int.zero_add] using certified
theorem check747 (p : Pattern) : (!walkGuard soko2_2.board support p 181 202 .southWest || decide (bonus 181 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound747 p)
theorem guard748 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 160 .north = true) : d4471 p = 1 := by
  change (!(p 182) && !(p 160) && !false) = true at guard
  cases h160 : p 160 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4206, d4471, h160, h182] at guard ⊢
theorem bound748 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 160 .north = true) : bonus 182 p ≤ bonus 160 p := by
  have certified := compare12090 p (guard748 p guard)
  simpa only [at182, at160, Int.zero_add] using certified
theorem check748 (p : Pattern) : (!walkGuard soko2_2.board support p 182 160 .north || decide (bonus 182 p ≤ bonus 160 p)) = true :=
  check_of_implication _ _ (bound748 p)
theorem guard749 (p : Pattern) (guard : pushGuard support p 182 160 138 138 = true) : d4208 p = 1 := by
  change (!(p 182) && (!true || (p 160)) && !(p 138) && (!(p 138) || false)) = true at guard
  cases h138 : p 138 <;> cases h160 : p 160 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4206, d4207, d4208, h138, h160, h182] at guard ⊢
theorem bound749 (p : Pattern) (guard : pushGuard support p 182 160 138 138 = true) : bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder 138 - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some 138)) := by
  have certified := compare12346 p (guard749 p guard)
  change d1681 p ≤ (2 : Int) + d789 (change p 160 (some 138))
  have normalized := agree789 _ _ (change_representative support p 160 (some 138) 10000 dummy_outside)
  rw [normalized]
  change d1681 p ≤ (2 : Int) + d789 (change p 160 (some 138))
  rw [sub7258]
  exact certified
theorem check749 (p : Pattern) : (!pushGuard support p 182 160 138 138 || decide (bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder 138 - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some 138)))) = true :=
  check_of_implication _ _ (bound749 p)
theorem guard750 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 204 .south = true) : d4967 p = 1 := by
  change (!(p 182) && !(p 204) && !false) = true at guard
  cases h182 : p 182 <;> cases h204 : p 204
  all_goals simp [d0, d1, d4474, d4967, h182, h204] at guard ⊢
theorem bound750 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 204 .south = true) : bonus 182 p ≤ bonus 204 p := by
  have certified := compare12708 p (guard750 p guard)
  simpa only [at182, at204, Int.zero_add] using certified
theorem check750 (p : Pattern) : (!walkGuard soko2_2.board support p 182 204 .south || decide (bonus 182 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound750 p)
theorem guard751 (p : Pattern) (guard : pushGuard support p 182 204 226 226 = true) : d4985 p = 1 := by
  change (!(p 182) && (!true || (p 204)) && !false && (!false || false)) = true at guard
  cases h182 : p 182 <;> cases h204 : p 204
  all_goals simp [d0, d1, d4473, d4985, h182, h204] at guard ⊢
theorem bound751 (p : Pattern) (guard : pushGuard support p 182 204 226 226 = true) : bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder 226 - Generated.soko2_2Potential.boulder 204 + bonus 204 (change p 204 (some 226)) := by
  have certified := compare13103 p (guard751 p guard)
  change d1681 p ≤ (0 : Int) + d2183 (change p 204 (some 226))
  have normalized := agree2183 _ _ (change_representative support p 204 (some 226) 10000 dummy_outside)
  rw [normalized]
  change d1681 p ≤ (0 : Int) + d2183 (change p 204 none)
  rw [sub7823]
  exact certified
theorem check751 (p : Pattern) : (!pushGuard support p 182 204 226 226 || decide (bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder 226 - Generated.soko2_2Potential.boulder 204 + bonus 204 (change p 204 (some 226)))) = true :=
  check_of_implication _ _ (bound751 p)
theorem guard752 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 181 .west = true) : d4206 p = 1 := by
  change (!(p 182) && !false && !false) = true at guard
  cases h182 : p 182
  all_goals simp [d0, d1, d4206, h182] at guard ⊢
theorem bound752 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 181 .west = true) : bonus 182 p ≤ bonus 181 p := by
  have certified := compare13245 p (guard752 p guard)
  simpa only [at182, at181, Int.zero_add] using certified
theorem check752 (p : Pattern) : (!walkGuard soko2_2.board support p 182 181 .west || decide (bonus 182 p ≤ bonus 181 p)) = true :=
  check_of_implication _ _ (bound752 p)
theorem guard753 (p : Pattern) (guard : pushGuard support p 182 181 180 180 = true) : d4206 p = 1 := by
  change (!(p 182) && (!false || false) && !false && (!false || false)) = true at guard
  cases h182 : p 182
  all_goals simp [d0, d1, d4206, h182] at guard ⊢
theorem bound753 (p : Pattern) (guard : pushGuard support p 182 181 180 180 = true) : bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder 180 - Generated.soko2_2Potential.boulder 181 + bonus 181 (change p 181 (some 180)) := by
  have certified := compare13480 p (guard753 p guard)
  change d1681 p ≤ (2 : Int) + d267 (change p 181 (some 180))
  have normalized := agree267 _ _ (change_representative support p 181 (some 180) 10000 dummy_outside)
  rw [normalized]
  change d1681 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check753 (p : Pattern) : (!pushGuard support p 182 181 180 180 || decide (bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder 180 - Generated.soko2_2Potential.boulder 181 + bonus 181 (change p 181 (some 180)))) = true :=
  check_of_implication _ _ (bound753 p)
theorem guard754 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 161 .northEast = true) : d4764 p = 1 := by
  change (!(p 182) && !(p 161) && !(true && (p 160) && true)) = true at guard
  cases h160 : p 160 <;> cases h161 : p 161 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4206, d4763, d4764, h160, h161, h182] at guard ⊢
theorem bound754 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 161 .northEast = true) : bonus 182 p ≤ bonus 161 p := by
  have certified := compare13654 p (guard754 p guard)
  simpa only [at182, at161, Int.zero_add] using certified
theorem check754 (p : Pattern) : (!walkGuard soko2_2.board support p 182 161 .northEast || decide (bonus 182 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound754 p)
theorem guard755 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 159 .northWest = true) : d4206 p = 1 := by
  change (!(p 182) && !false && !(true && (p 160) && false)) = true at guard
  cases h160 : p 160 <;> cases h182 : p 182
  all_goals simp [d0, d1, d4206, h160, h182] at guard ⊢
theorem bound755 (p : Pattern) (guard : walkGuard soko2_2.board support p 182 159 .northWest = true) : bonus 182 p ≤ bonus 159 p := by
  have certified := compare13245 p (guard755 p guard)
  simpa only [at182, at159, Int.zero_add] using certified
theorem check755 (p : Pattern) : (!walkGuard soko2_2.board support p 182 159 .northWest || decide (bonus 182 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound755 p)
theorem guard756 (p : Pattern) (guard : walkGuard soko2_2.board support p 184 162 .north = true) : d4395 p = 1 := by
  change (!false && !(p 162) && !false) = true at guard
  cases h162 : p 162
  all_goals simp [d0, d1, d4395, h162] at guard ⊢
theorem bound756 (p : Pattern) (guard : walkGuard soko2_2.board support p 184 162 .north = true) : bonus 184 p ≤ bonus 162 p := by
  have certified := compare13827 p (guard756 p guard)
  simpa only [at184, at162, Int.zero_add] using certified
theorem check756 (p : Pattern) : (!walkGuard soko2_2.board support p 184 162 .north || decide (bonus 184 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound756 p)
theorem guard757 (p : Pattern) (guard : walkGuard soko2_2.board support p 184 185 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound757 (p : Pattern) (guard : walkGuard soko2_2.board support p 184 185 .east = true) : bonus 184 p ≤ bonus 185 p := by
  have certified := compare10636 p (guard757 p guard)
  simpa only [at184, at185, Int.zero_add] using certified
theorem check757 (p : Pattern) : (!walkGuard soko2_2.board support p 184 185 .east || decide (bonus 184 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound757 p)
theorem guard758 (p : Pattern) (guard : pushGuard support p 184 185 186 186 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound758 (p : Pattern) (guard : pushGuard support p 184 185 186 186 = true) : bonus 184 p ≤ 1 + Generated.soko2_2Potential.boulder 186 - Generated.soko2_2Potential.boulder 185 + bonus 185 (change p 185 (some 186)) := by
  have certified := compare13828 p (guard758 p guard)
  change d1503 p ≤ (1 : Int) + d1503 (change p 185 (some 186))
  have normalized := agree1503 _ _ (change_representative support p 185 (some 186) 10000 dummy_outside)
  rw [normalized]
  change d1503 p ≤ (1 : Int) + d1503 (change p 10000 none)
  rw [sub7977]
  exact certified
theorem check758 (p : Pattern) : (!pushGuard support p 184 185 186 186 || decide (bonus 184 p ≤ 1 + Generated.soko2_2Potential.boulder 186 - Generated.soko2_2Potential.boulder 185 + bonus 185 (change p 185 (some 186)))) = true :=
  check_of_implication _ _ (bound758 p)
theorem guard759 (p : Pattern) (guard : walkGuard soko2_2.board support p 184 163 .northEast = true) : d4148 p = 1 := by
  change (!false && !(p 163) && !(true && (p 162) && false)) = true at guard
  cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4148, h162, h163] at guard ⊢
theorem bound759 (p : Pattern) (guard : walkGuard soko2_2.board support p 184 163 .northEast = true) : bonus 184 p ≤ bonus 163 p := by
  have certified := compare10838 p (guard759 p guard)
  simpa only [at184, at163, Int.zero_add] using certified
theorem check759 (p : Pattern) : (!walkGuard soko2_2.board support p 184 163 .northEast || decide (bonus 184 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound759 p)
theorem guard760 (p : Pattern) (guard : walkGuard soko2_2.board support p 184 161 .northWest = true) : d4670 p = 1 := by
  change (!false && !(p 161) && !(true && (p 162) && true)) = true at guard
  cases h161 : p 161 <;> cases h162 : p 162
  all_goals simp [d0, d1, d4395, d4670, h161, h162] at guard ⊢
theorem bound760 (p : Pattern) (guard : walkGuard soko2_2.board support p 184 161 .northWest = true) : bonus 184 p ≤ bonus 161 p := by
  have certified := compare14020 p (guard760 p guard)
  simpa only [at184, at161, Int.zero_add] using certified
theorem check760 (p : Pattern) : (!walkGuard soko2_2.board support p 184 161 .northWest || decide (bonus 184 p ≤ bonus 161 p)) = true :=
  check_of_implication _ _ (bound760 p)
theorem guard761 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 163 .north = true) : d4148 p = 1 := by
  change (!false && !(p 163) && !false) = true at guard
  cases h163 : p 163
  all_goals simp [d0, d1, d4148, h163] at guard ⊢
theorem bound761 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 163 .north = true) : bonus 185 p ≤ bonus 163 p := by
  have certified := compare10838 p (guard761 p guard)
  simpa only [at185, at163, Int.zero_add] using certified
theorem check761 (p : Pattern) : (!walkGuard soko2_2.board support p 185 163 .north || decide (bonus 185 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound761 p)
theorem guard762 (p : Pattern) (guard : pushGuard support p 185 163 141 141 = true) : d4304 p = 1 := by
  change (!false && (!true || (p 163)) && !(p 141) && (!(p 141) || false)) = true at guard
  cases h141 : p 141 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4147, d4304, h141, h163] at guard ⊢
theorem bound762 (p : Pattern) (guard : pushGuard support p 185 163 141 141 = true) : bonus 185 p ≤ 1 + Generated.soko2_2Potential.boulder 141 - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some 141)) := by
  have certified := compare14198 p (guard762 p guard)
  change d1503 p ≤ (2 : Int) + d1398 (change p 163 (some 141))
  have normalized := agree1398 _ _ (change_representative support p 163 (some 141) 10000 dummy_outside)
  rw [normalized]
  change d1503 p ≤ (2 : Int) + d1398 (change p 163 (some 141))
  rw [sub8183]
  exact certified
theorem check762 (p : Pattern) : (!pushGuard support p 185 163 141 141 || decide (bonus 185 p ≤ 1 + Generated.soko2_2Potential.boulder 141 - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some 141)))) = true :=
  check_of_implication _ _ (bound762 p)
theorem guard763 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 186 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound763 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 186 .east = true) : bonus 185 p ≤ bonus 186 p := by
  have certified := compare10636 p (guard763 p guard)
  simpa only [at185, at186, Int.zero_add] using certified
theorem check763 (p : Pattern) : (!walkGuard soko2_2.board support p 185 186 .east || decide (bonus 185 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound763 p)
theorem guard764 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 184 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound764 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 184 .west = true) : bonus 185 p ≤ bonus 184 p := by
  have certified := compare10636 p (guard764 p guard)
  simpa only [at185, at184, Int.zero_add] using certified
theorem check764 (p : Pattern) : (!walkGuard soko2_2.board support p 185 184 .west || decide (bonus 185 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound764 p)
theorem guard765 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 164 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 163) && false)) = true at guard
  cases h163 : p 163
  all_goals simp [d1, h163] at guard ⊢
theorem bound765 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 164 .northEast = true) : bonus 185 p ≤ bonus 164 p := by
  have certified := compare10636 p (guard765 p guard)
  simpa only [at185, at164, Int.zero_add] using certified
theorem check765 (p : Pattern) : (!walkGuard soko2_2.board support p 185 164 .northEast || decide (bonus 185 p ≤ bonus 164 p)) = true :=
  check_of_implication _ _ (bound765 p)
theorem guard766 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 162 .northWest = true) : d4395 p = 1 := by
  change (!false && !(p 162) && !(true && (p 163) && false)) = true at guard
  cases h162 : p 162 <;> cases h163 : p 163
  all_goals simp [d0, d1, d4395, h162, h163] at guard ⊢
theorem bound766 (p : Pattern) (guard : walkGuard soko2_2.board support p 185 162 .northWest = true) : bonus 185 p ≤ bonus 162 p := by
  have certified := compare13827 p (guard766 p guard)
  simpa only [at185, at162, Int.zero_add] using certified
theorem check766 (p : Pattern) : (!walkGuard soko2_2.board support p 185 162 .northWest || decide (bonus 185 p ≤ bonus 162 p)) = true :=
  check_of_implication _ _ (bound766 p)
theorem guard767 (p : Pattern) (guard : walkGuard soko2_2.board support p 186 164 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound767 (p : Pattern) (guard : walkGuard soko2_2.board support p 186 164 .north = true) : bonus 186 p ≤ bonus 164 p := by
  have certified := compare10636 p (guard767 p guard)
  simpa only [at186, at164, Int.zero_add] using certified
theorem check767 (p : Pattern) : (!walkGuard soko2_2.board support p 186 164 .north || decide (bonus 186 p ≤ bonus 164 p)) = true :=
  check_of_implication _ _ (bound767 p)
end NetHack.Sokoban22Refined85
