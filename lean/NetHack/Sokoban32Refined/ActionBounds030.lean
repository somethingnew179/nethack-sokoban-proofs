import NetHack.Sokoban32Refined.ActionBounds029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard720 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 136 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound720 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 136 .northWest = true) : bonus 163 p ≤ bonus 136 p := by
  have certified := compare0 p (guard720 p guard)
  simpa only [at163, at136, Int.zero_add] using certified
theorem check720 (p : Pattern) : (!walkGuard soko3_2.board support p 163 136 .northWest || decide (bonus 163 p ≤ bonus 136 p)) = true :=
  check_of_implication _ _ (bound720 p)
theorem guard721 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 188 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound721 (p : Pattern) (guard : walkGuard soko3_2.board support p 163 188 .southWest = true) : bonus 163 p ≤ bonus 188 p := by
  have certified := compare0 p (guard721 p guard)
  simpa only [at163, at188, Int.zero_add] using certified
theorem check721 (p : Pattern) : (!walkGuard soko3_2.board support p 163 188 .southWest || decide (bonus 163 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound721 p)
theorem guard722 (p : Pattern) (guard : walkGuard soko3_2.board support p 165 139 .north = true) : d1088 p = 1 := by
  change (!false && !(p 139) && !false) = true at guard
  cases h139 : p 139
  all_goals simp [d0, d1, d1088, h139] at guard ⊢
theorem bound722 (p : Pattern) (guard : walkGuard soko3_2.board support p 165 139 .north = true) : bonus 165 p ≤ bonus 139 p := by
  have certified := compare9249 p (guard722 p guard)
  simpa only [at165, at139, Int.zero_add] using certified
theorem check722 (p : Pattern) : (!walkGuard soko3_2.board support p 165 139 .north || decide (bonus 165 p ≤ bonus 139 p)) = true :=
  check_of_implication _ _ (bound722 p)
theorem guard723 (p : Pattern) (guard : pushGuard support p 165 139 113 113 = true) : d1096 p = 1 := by
  change (!false && (!true || (p 139)) && !(p 113) && (!(p 113) || false)) = true at guard
  cases h113 : p 113 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1087, d1096, h113, h139] at guard ⊢
theorem bound723 (p : Pattern) (guard : pushGuard support p 165 139 113 113 = true) : bonus 165 p ≤ 1 + Generated.soko3_2Potential.boulder 113 - Generated.soko3_2Potential.boulder 139 + bonus 139 (change p 139 (some 113)) := by
  have certified := compare9294 p (guard723 p guard)
  change d134 p ≤ (1 : Int) + d537 (change p 139 (some 113))
  have normalized := agree537 _ _ (change_representative support p 139 (some 113) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d537 (change p 139 (some 113))
  rw [sub3440]
  exact certified
theorem check723 (p : Pattern) : (!pushGuard support p 165 139 113 113 || decide (bonus 165 p ≤ 1 + Generated.soko3_2Potential.boulder 113 - Generated.soko3_2Potential.boulder 139 + bonus 139 (change p 139 (some 113)))) = true :=
  check_of_implication _ _ (bound723 p)
theorem guard724 (p : Pattern) (guard : walkGuard soko3_2.board support p 165 166 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound724 (p : Pattern) (guard : walkGuard soko3_2.board support p 165 166 .east = true) : bonus 165 p ≤ bonus 166 p := by
  have certified := compare0 p (guard724 p guard)
  simpa only [at165, at166, Int.zero_add] using certified
theorem check724 (p : Pattern) : (!walkGuard soko3_2.board support p 165 166 .east || decide (bonus 165 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound724 p)
theorem guard725 (p : Pattern) (guard : walkGuard soko3_2.board support p 165 138 .northWest = true) : d1092 p = 1 := by
  change (!false && !(p 138) && !(true && (p 139) && true)) = true at guard
  cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1092, h138, h139] at guard ⊢
theorem bound725 (p : Pattern) (guard : walkGuard soko3_2.board support p 165 138 .northWest = true) : bonus 165 p ≤ bonus 138 p := by
  have certified := compare9359 p (guard725 p guard)
  simpa only [at165, at138, Int.zero_add] using certified
theorem check725 (p : Pattern) : (!walkGuard soko3_2.board support p 165 138 .northWest || decide (bonus 165 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound725 p)
theorem guard726 (p : Pattern) (guard : walkGuard soko3_2.board support p 165 192 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound726 (p : Pattern) (guard : walkGuard soko3_2.board support p 165 192 .southEast = true) : bonus 165 p ≤ bonus 192 p := by
  have certified := compare0 p (guard726 p guard)
  simpa only [at165, at192, Int.zero_add] using certified
theorem check726 (p : Pattern) : (!walkGuard soko3_2.board support p 165 192 .southEast || decide (bonus 165 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound726 p)
theorem guard727 (p : Pattern) (guard : walkGuard soko3_2.board support p 166 192 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound727 (p : Pattern) (guard : walkGuard soko3_2.board support p 166 192 .south = true) : bonus 166 p ≤ bonus 192 p := by
  have certified := compare0 p (guard727 p guard)
  simpa only [at166, at192, Int.zero_add] using certified
theorem check727 (p : Pattern) : (!walkGuard soko3_2.board support p 166 192 .south || decide (bonus 166 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound727 p)
theorem guard728 (p : Pattern) (guard : pushGuard support p 166 192 218 218 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound728 (p : Pattern) (guard : pushGuard support p 166 192 218 218 = true) : bonus 166 p ≤ 1 + Generated.soko3_2Potential.boulder 218 - Generated.soko3_2Potential.boulder 192 + bonus 192 (change p 192 (some 218)) := by
  have certified := compare0 p (guard728 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 192 (some 218))
  have normalized := agree134 _ _ (change_representative support p 192 (some 218) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check728 (p : Pattern) : (!pushGuard support p 166 192 218 218 || decide (bonus 166 p ≤ 1 + Generated.soko3_2Potential.boulder 218 - Generated.soko3_2Potential.boulder 192 + bonus 192 (change p 192 (some 218)))) = true :=
  check_of_implication _ _ (bound728 p)
theorem guard729 (p : Pattern) (guard : walkGuard soko3_2.board support p 166 165 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound729 (p : Pattern) (guard : walkGuard soko3_2.board support p 166 165 .west = true) : bonus 166 p ≤ bonus 165 p := by
  have certified := compare0 p (guard729 p guard)
  simpa only [at166, at165, Int.zero_add] using certified
theorem check729 (p : Pattern) : (!walkGuard soko3_2.board support p 166 165 .west || decide (bonus 166 p ≤ bonus 165 p)) = true :=
  check_of_implication _ _ (bound729 p)
theorem guard730 (p : Pattern) (guard : walkGuard soko3_2.board support p 166 139 .northWest = true) : d1088 p = 1 := by
  change (!false && !(p 139) && !(true && true && false)) = true at guard
  cases h139 : p 139
  all_goals simp [d0, d1, d1088, h139] at guard ⊢
theorem bound730 (p : Pattern) (guard : walkGuard soko3_2.board support p 166 139 .northWest = true) : bonus 166 p ≤ bonus 139 p := by
  have certified := compare9249 p (guard730 p guard)
  simpa only [at166, at139, Int.zero_add] using certified
theorem check730 (p : Pattern) : (!walkGuard soko3_2.board support p 166 139 .northWest || decide (bonus 166 p ≤ bonus 139 p)) = true :=
  check_of_implication _ _ (bound730 p)
theorem guard731 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 146 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound731 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 146 .north = true) : bonus 172 p ≤ bonus 146 p := by
  have certified := compare103 p (guard731 p guard)
  simpa only [at172, at146, Int.zero_add] using certified
theorem check731 (p : Pattern) : (!walkGuard soko3_2.board support p 172 146 .north || decide (bonus 172 p ≤ bonus 146 p)) = true :=
  check_of_implication _ _ (bound731 p)
theorem guard732 (p : Pattern) (guard : pushGuard support p 172 146 120 120 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound732 (p : Pattern) (guard : pushGuard support p 172 146 120 120 = true) : bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder 120 - Generated.soko3_2Potential.boulder 146 + bonus 146 (change p 146 (some 120)) := by
  have certified := compare37 p (guard732 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 146 (some 120))
  have normalized := agree0 _ _ (change_representative support p 146 (some 120) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check732 (p : Pattern) : (!pushGuard support p 172 146 120 120 || decide (bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder 120 - Generated.soko3_2Potential.boulder 146 + bonus 146 (change p 146 (some 120)))) = true :=
  check_of_implication _ _ (bound732 p)
theorem guard733 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 198 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound733 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 198 .south = true) : bonus 172 p ≤ bonus 198 p := by
  have certified := compare103 p (guard733 p guard)
  simpa only [at172, at198, Int.zero_add] using certified
theorem check733 (p : Pattern) : (!walkGuard soko3_2.board support p 172 198 .south || decide (bonus 172 p ≤ bonus 198 p)) = true :=
  check_of_implication _ _ (bound733 p)
theorem guard734 (p : Pattern) (guard : pushGuard support p 172 198 224 224 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound734 (p : Pattern) (guard : pushGuard support p 172 198 224 224 = true) : bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder 224 - Generated.soko3_2Potential.boulder 198 + bonus 198 (change p 198 (some 224)) := by
  have certified := compare37 p (guard734 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 198 (some 224))
  have normalized := agree0 _ _ (change_representative support p 198 (some 224) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check734 (p : Pattern) : (!pushGuard support p 172 198 224 224 || decide (bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder 224 - Generated.soko3_2Potential.boulder 198 + bonus 198 (change p 198 (some 224)))) = true :=
  check_of_implication _ _ (bound734 p)
theorem guard735 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 173 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound735 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 173 .east = true) : bonus 172 p ≤ bonus 173 p := by
  have certified := compare103 p (guard735 p guard)
  simpa only [at172, at173, Int.zero_add] using certified
theorem check735 (p : Pattern) : (!walkGuard soko3_2.board support p 172 173 .east || decide (bonus 172 p ≤ bonus 173 p)) = true :=
  check_of_implication _ _ (bound735 p)
theorem guard736 (p : Pattern) (guard : pushGuard support p 172 173 174 174 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound736 (p : Pattern) (guard : pushGuard support p 172 173 174 174 = true) : bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some 174)) := by
  have certified := compare37 p (guard736 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 173 (some 174))
  have normalized := agree0 _ _ (change_representative support p 173 (some 174) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check736 (p : Pattern) : (!pushGuard support p 172 173 174 174 || decide (bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some 174)))) = true :=
  check_of_implication _ _ (bound736 p)
theorem guard737 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 147 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound737 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 147 .northEast = true) : bonus 172 p ≤ bonus 147 p := by
  have certified := compare103 p (guard737 p guard)
  simpa only [at172, at147, Int.zero_add] using certified
theorem check737 (p : Pattern) : (!walkGuard soko3_2.board support p 172 147 .northEast || decide (bonus 172 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound737 p)
theorem guard738 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 199 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound738 (p : Pattern) (guard : walkGuard soko3_2.board support p 172 199 .southEast = true) : bonus 172 p ≤ bonus 199 p := by
  have certified := compare103 p (guard738 p guard)
  simpa only [at172, at199, Int.zero_add] using certified
theorem check738 (p : Pattern) : (!walkGuard soko3_2.board support p 172 199 .southEast || decide (bonus 172 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound738 p)
theorem guard739 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 147 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound739 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 147 .north = true) : bonus 173 p ≤ bonus 147 p := by
  have certified := compare103 p (guard739 p guard)
  simpa only [at173, at147, Int.zero_add] using certified
theorem check739 (p : Pattern) : (!walkGuard soko3_2.board support p 173 147 .north || decide (bonus 173 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound739 p)
theorem guard740 (p : Pattern) (guard : pushGuard support p 173 147 121 121 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound740 (p : Pattern) (guard : pushGuard support p 173 147 121 121 = true) : bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some 121)) := by
  have certified := compare37 p (guard740 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 147 (some 121))
  have normalized := agree0 _ _ (change_representative support p 147 (some 121) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check740 (p : Pattern) : (!pushGuard support p 173 147 121 121 || decide (bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some 121)))) = true :=
  check_of_implication _ _ (bound740 p)
theorem guard741 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 199 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound741 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 199 .south = true) : bonus 173 p ≤ bonus 199 p := by
  have certified := compare103 p (guard741 p guard)
  simpa only [at173, at199, Int.zero_add] using certified
theorem check741 (p : Pattern) : (!walkGuard soko3_2.board support p 173 199 .south || decide (bonus 173 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound741 p)
theorem guard742 (p : Pattern) (guard : pushGuard support p 173 199 225 225 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound742 (p : Pattern) (guard : pushGuard support p 173 199 225 225 = true) : bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder 225 - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some 225)) := by
  have certified := compare37 p (guard742 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 199 (some 225))
  have normalized := agree0 _ _ (change_representative support p 199 (some 225) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check742 (p : Pattern) : (!pushGuard support p 173 199 225 225 || decide (bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder 225 - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some 225)))) = true :=
  check_of_implication _ _ (bound742 p)
theorem guard743 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 174 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound743 (p : Pattern) (guard : walkGuard soko3_2.board support p 173 174 .east = true) : bonus 173 p ≤ bonus 174 p := by
  have certified := compare103 p (guard743 p guard)
  simpa only [at173, at174, Int.zero_add] using certified
theorem check743 (p : Pattern) : (!walkGuard soko3_2.board support p 173 174 .east || decide (bonus 173 p ≤ bonus 174 p)) = true :=
  check_of_implication _ _ (bound743 p)
end NetHack.Sokoban32Refined
