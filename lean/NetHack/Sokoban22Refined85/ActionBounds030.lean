import NetHack.Sokoban22Refined85.ActionBounds029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard720 (p : Pattern) (guard : pushGuard support p 172 150 128 128 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound720 (p : Pattern) (guard : pushGuard support p 172 150 128 128 = true) : bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder 128 - Generated.soko2_2Potential.boulder 150 + bonus 150 (change p 150 (some 128)) := by
  have certified := compare1087 p (guard720 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 150 (some 128))
  have normalized := agree0 _ _ (change_representative support p 150 (some 128) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check720 (p : Pattern) : (!pushGuard support p 172 150 128 128 || decide (bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder 128 - Generated.soko2_2Potential.boulder 150 + bonus 150 (change p 150 (some 128)))) = true :=
  check_of_implication _ _ (bound720 p)
theorem guard721 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 194 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound721 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 194 .south = true) : bonus 172 p ≤ bonus 194 p := by
  have certified := compare1086 p (guard721 p guard)
  simpa only [at172, at194, Int.zero_add] using certified
theorem check721 (p : Pattern) : (!walkGuard soko2_2.board support p 172 194 .south || decide (bonus 172 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound721 p)
theorem guard722 (p : Pattern) (guard : pushGuard support p 172 194 216 216 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound722 (p : Pattern) (guard : pushGuard support p 172 194 216 216 = true) : bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder 216 - Generated.soko2_2Potential.boulder 194 + bonus 194 (change p 194 (some 216)) := by
  have certified := compare1087 p (guard722 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 194 (some 216))
  have normalized := agree0 _ _ (change_representative support p 194 (some 216) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check722 (p : Pattern) : (!pushGuard support p 172 194 216 216 || decide (bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder 216 - Generated.soko2_2Potential.boulder 194 + bonus 194 (change p 194 (some 216)))) = true :=
  check_of_implication _ _ (bound722 p)
theorem guard723 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 171 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound723 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 171 .west = true) : bonus 172 p ≤ bonus 171 p := by
  have certified := compare1086 p (guard723 p guard)
  simpa only [at172, at171, Int.zero_add] using certified
theorem check723 (p : Pattern) : (!walkGuard soko2_2.board support p 172 171 .west || decide (bonus 172 p ≤ bonus 171 p)) = true :=
  check_of_implication _ _ (bound723 p)
theorem guard724 (p : Pattern) (guard : pushGuard support p 172 171 170 170 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound724 (p : Pattern) (guard : pushGuard support p 172 171 170 170 = true) : bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some 170)) := by
  have certified := compare1087 p (guard724 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 171 (some 170))
  have normalized := agree0 _ _ (change_representative support p 171 (some 170) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check724 (p : Pattern) : (!pushGuard support p 172 171 170 170 || decide (bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some 170)))) = true :=
  check_of_implication _ _ (bound724 p)
theorem guard725 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 149 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound725 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 149 .northWest = true) : bonus 172 p ≤ bonus 149 p := by
  have certified := compare1086 p (guard725 p guard)
  simpa only [at172, at149, Int.zero_add] using certified
theorem check725 (p : Pattern) : (!walkGuard soko2_2.board support p 172 149 .northWest || decide (bonus 172 p ≤ bonus 149 p)) = true :=
  check_of_implication _ _ (bound725 p)
theorem guard726 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 193 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound726 (p : Pattern) (guard : walkGuard soko2_2.board support p 172 193 .southWest = true) : bonus 172 p ≤ bonus 193 p := by
  have certified := compare1086 p (guard726 p guard)
  simpa only [at172, at193, Int.zero_add] using certified
theorem check726 (p : Pattern) : (!walkGuard soko2_2.board support p 172 193 .southWest || decide (bonus 172 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound726 p)
theorem guard727 (p : Pattern) (guard : walkGuard soko2_2.board support p 177 155 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound727 (p : Pattern) (guard : walkGuard soko2_2.board support p 177 155 .north = true) : bonus 177 p ≤ bonus 155 p := by
  have certified := compare0 p (guard727 p guard)
  simpa only [at177, at155, Int.zero_add] using certified
theorem check727 (p : Pattern) : (!walkGuard soko2_2.board support p 177 155 .north || decide (bonus 177 p ≤ bonus 155 p)) = true :=
  check_of_implication _ _ (bound727 p)
theorem guard728 (p : Pattern) (guard : pushGuard support p 177 155 133 133 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound728 (p : Pattern) (guard : pushGuard support p 177 155 133 133 = true) : bonus 177 p ≤ 1 + Generated.soko2_2Potential.boulder 133 - Generated.soko2_2Potential.boulder 155 + bonus 155 (change p 155 (some 133)) := by
  have certified := compare1 p (guard728 p guard)
  change d267 p ≤ (1 : Int) + d267 (change p 155 (some 133))
  have normalized := agree267 _ _ (change_representative support p 155 (some 133) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (1 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check728 (p : Pattern) : (!pushGuard support p 177 155 133 133 || decide (bonus 177 p ≤ 1 + Generated.soko2_2Potential.boulder 133 - Generated.soko2_2Potential.boulder 155 + bonus 155 (change p 155 (some 133)))) = true :=
  check_of_implication _ _ (bound728 p)
theorem guard729 (p : Pattern) (guard : walkGuard soko2_2.board support p 177 199 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound729 (p : Pattern) (guard : walkGuard soko2_2.board support p 177 199 .south = true) : bonus 177 p ≤ bonus 199 p := by
  have certified := compare0 p (guard729 p guard)
  simpa only [at177, at199, Int.zero_add] using certified
theorem check729 (p : Pattern) : (!walkGuard soko2_2.board support p 177 199 .south || decide (bonus 177 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound729 p)
theorem guard730 (p : Pattern) (guard : walkGuard soko2_2.board support p 177 156 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound730 (p : Pattern) (guard : walkGuard soko2_2.board support p 177 156 .northEast = true) : bonus 177 p ≤ bonus 156 p := by
  have certified := compare0 p (guard730 p guard)
  simpa only [at177, at156, Int.zero_add] using certified
theorem check730 (p : Pattern) : (!walkGuard soko2_2.board support p 177 156 .northEast || decide (bonus 177 p ≤ bonus 156 p)) = true :=
  check_of_implication _ _ (bound730 p)
theorem guard731 (p : Pattern) (guard : walkGuard soko2_2.board support p 177 200 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound731 (p : Pattern) (guard : walkGuard soko2_2.board support p 177 200 .southEast = true) : bonus 177 p ≤ bonus 200 p := by
  have certified := compare0 p (guard731 p guard)
  simpa only [at177, at200, Int.zero_add] using certified
theorem check731 (p : Pattern) : (!walkGuard soko2_2.board support p 177 200 .southEast || decide (bonus 177 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound731 p)
theorem guard732 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 158 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound732 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 158 .north = true) : bonus 180 p ≤ bonus 158 p := by
  have certified := compare0 p (guard732 p guard)
  simpa only [at180, at158, Int.zero_add] using certified
theorem check732 (p : Pattern) : (!walkGuard soko2_2.board support p 180 158 .north || decide (bonus 180 p ≤ bonus 158 p)) = true :=
  check_of_implication _ _ (bound732 p)
theorem guard733 (p : Pattern) (guard : pushGuard support p 180 158 136 136 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound733 (p : Pattern) (guard : pushGuard support p 180 158 136 136 = true) : bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder 136 - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some 136)) := by
  have certified := compare2458 p (guard733 p guard)
  change d267 p ≤ (2 : Int) + d267 (change p 158 (some 136))
  have normalized := agree267 _ _ (change_representative support p 158 (some 136) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check733 (p : Pattern) : (!pushGuard support p 180 158 136 136 || decide (bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder 136 - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some 136)))) = true :=
  check_of_implication _ _ (bound733 p)
theorem guard734 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 202 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound734 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 202 .south = true) : bonus 180 p ≤ bonus 202 p := by
  have certified := compare0 p (guard734 p guard)
  simpa only [at180, at202, Int.zero_add] using certified
theorem check734 (p : Pattern) : (!walkGuard soko2_2.board support p 180 202 .south || decide (bonus 180 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound734 p)
theorem guard735 (p : Pattern) (guard : pushGuard support p 180 202 224 224 = true) : d4902 p = 1 := by
  change (!false && (!false || false) && !(p 224) && (!(p 224) || false)) = true at guard
  cases h224 : p 224
  all_goals simp [d0, d1, d4902, h224] at guard ⊢
theorem bound735 (p : Pattern) (guard : pushGuard support p 180 202 224 224 = true) : bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder 224 - Generated.soko2_2Potential.boulder 202 + bonus 202 (change p 202 (some 224)) := by
  have certified := compare11206 p (guard735 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 202 (some 224))
  have normalized := agree267 _ _ (change_representative support p 202 (some 224) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 (some 224))
  rw [sub6825]
  exact certified
theorem check735 (p : Pattern) : (!pushGuard support p 180 202 224 224 || decide (bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder 224 - Generated.soko2_2Potential.boulder 202 + bonus 202 (change p 202 (some 224)))) = true :=
  check_of_implication _ _ (bound735 p)
theorem guard736 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 181 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound736 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 181 .east = true) : bonus 180 p ≤ bonus 181 p := by
  have certified := compare0 p (guard736 p guard)
  simpa only [at180, at181, Int.zero_add] using certified
theorem check736 (p : Pattern) : (!walkGuard soko2_2.board support p 180 181 .east || decide (bonus 180 p ≤ bonus 181 p)) = true :=
  check_of_implication _ _ (bound736 p)
theorem guard737 (p : Pattern) (guard : pushGuard support p 180 181 182 182 = true) : d4206 p = 1 := by
  change (!false && (!false || false) && !(p 182) && (!(p 182) || false)) = true at guard
  cases h182 : p 182
  all_goals simp [d0, d1, d4206, h182] at guard ⊢
theorem bound737 (p : Pattern) (guard : pushGuard support p 180 181 182 182 = true) : bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder 182 - Generated.soko2_2Potential.boulder 181 + bonus 181 (change p 181 (some 182)) := by
  have certified := compare11449 p (guard737 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 181 (some 182))
  have normalized := agree267 _ _ (change_representative support p 181 (some 182) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 (some 182))
  rw [sub7093]
  exact certified
theorem check737 (p : Pattern) : (!pushGuard support p 180 181 182 182 || decide (bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder 182 - Generated.soko2_2Potential.boulder 181 + bonus 181 (change p 181 (some 182)))) = true :=
  check_of_implication _ _ (bound737 p)
theorem guard738 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 159 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound738 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 159 .northEast = true) : bonus 180 p ≤ bonus 159 p := by
  have certified := compare0 p (guard738 p guard)
  simpa only [at180, at159, Int.zero_add] using certified
theorem check738 (p : Pattern) : (!walkGuard soko2_2.board support p 180 159 .northEast || decide (bonus 180 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound738 p)
theorem guard739 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 157 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound739 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 157 .northWest = true) : bonus 180 p ≤ bonus 157 p := by
  have certified := compare0 p (guard739 p guard)
  simpa only [at180, at157, Int.zero_add] using certified
theorem check739 (p : Pattern) : (!walkGuard soko2_2.board support p 180 157 .northWest || decide (bonus 180 p ≤ bonus 157 p)) = true :=
  check_of_implication _ _ (bound739 p)
theorem guard740 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 201 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound740 (p : Pattern) (guard : walkGuard soko2_2.board support p 180 201 .southWest = true) : bonus 180 p ≤ bonus 201 p := by
  have certified := compare0 p (guard740 p guard)
  simpa only [at180, at201, Int.zero_add] using certified
theorem check740 (p : Pattern) : (!walkGuard soko2_2.board support p 180 201 .southWest || decide (bonus 180 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound740 p)
theorem guard741 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 159 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound741 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 159 .north = true) : bonus 181 p ≤ bonus 159 p := by
  have certified := compare0 p (guard741 p guard)
  simpa only [at181, at159, Int.zero_add] using certified
theorem check741 (p : Pattern) : (!walkGuard soko2_2.board support p 181 159 .north || decide (bonus 181 p ≤ bonus 159 p)) = true :=
  check_of_implication _ _ (bound741 p)
theorem guard742 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 182 .east = true) : d4206 p = 1 := by
  change (!false && !(p 182) && !false) = true at guard
  cases h182 : p 182
  all_goals simp [d0, d1, d4206, h182] at guard ⊢
theorem bound742 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 182 .east = true) : bonus 181 p ≤ bonus 182 p := by
  have certified := compare5328 p (guard742 p guard)
  simpa only [at181, at182, Int.zero_add] using certified
theorem check742 (p : Pattern) : (!walkGuard soko2_2.board support p 181 182 .east || decide (bonus 181 p ≤ bonus 182 p)) = true :=
  check_of_implication _ _ (bound742 p)
theorem guard743 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 180 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound743 (p : Pattern) (guard : walkGuard soko2_2.board support p 181 180 .west = true) : bonus 181 p ≤ bonus 180 p := by
  have certified := compare0 p (guard743 p guard)
  simpa only [at181, at180, Int.zero_add] using certified
theorem check743 (p : Pattern) : (!walkGuard soko2_2.board support p 181 180 .west || decide (bonus 181 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound743 p)
end NetHack.Sokoban22Refined85
