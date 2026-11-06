import NetHack.Sokoban32Refined.ActionBounds022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard552 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 112 .north = true) : d1072 p = 1 := by
  change (!(p 138) && !(p 112) && !false) = true at guard
  cases h112 : p 112 <;> cases h138 : p 138
  all_goals simp [d0, d1, d857, d1072, h112, h138] at guard ⊢
theorem bound552 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 112 .north = true) : bonus 138 p ≤ bonus 112 p := by
  have certified := compare5274 p (guard552 p guard)
  simpa only [at138, at112, Int.zero_add] using certified
theorem check552 (p : Pattern) : (!walkGuard soko3_2.board support p 138 112 .north || decide (bonus 138 p ≤ bonus 112 p)) = true :=
  check_of_implication _ _ (bound552 p)
theorem guard553 (p : Pattern) (guard : pushGuard support p 138 112 86 86 = true) : d859 p = 1 := by
  change (!(p 138) && (!true || (p 112)) && !(p 86) && (!(p 86) || false)) = true at guard
  cases h86 : p 86 <;> cases h112 : p 112 <;> cases h138 : p 138
  all_goals simp [d0, d1, d857, d858, d859, h86, h112, h138] at guard ⊢
theorem bound553 (p : Pattern) (guard : pushGuard support p 138 112 86 86 = true) : bonus 138 p ≤ 1 + Generated.soko3_2Potential.boulder 86 - Generated.soko3_2Potential.boulder 112 + bonus 112 (change p 112 (some 86)) := by
  have certified := compare5361 p (guard553 p guard)
  change d455 p ≤ (2 : Int) + d227 (change p 112 (some 86))
  have normalized := agree227 _ _ (change_representative support p 112 (some 86) 10000 dummy_outside)
  rw [normalized]
  change d455 p ≤ (2 : Int) + d227 (change p 112 (some 86))
  rw [sub2475]
  exact certified
theorem check553 (p : Pattern) : (!pushGuard support p 138 112 86 86 || decide (bonus 138 p ≤ 1 + Generated.soko3_2Potential.boulder 86 - Generated.soko3_2Potential.boulder 112 + bonus 112 (change p 112 (some 86)))) = true :=
  check_of_implication _ _ (bound553 p)
theorem guard554 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 139 .east = true) : d1092 p = 1 := by
  change (!(p 138) && !(p 139) && !false) = true at guard
  cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1092, h138, h139] at guard ⊢
theorem bound554 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 139 .east = true) : bonus 138 p ≤ bonus 139 p := by
  have certified := compare5472 p (guard554 p guard)
  simpa only [at138, at139, Int.zero_add] using certified
theorem check554 (p : Pattern) : (!walkGuard soko3_2.board support p 138 139 .east || decide (bonus 138 p ≤ bonus 139 p)) = true :=
  check_of_implication _ _ (bound554 p)
theorem guard555 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 137 .west = true) : d857 p = 1 := by
  change (!(p 138) && !false && !false) = true at guard
  cases h138 : p 138
  all_goals simp [d0, d1, d857, h138] at guard ⊢
theorem bound555 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 137 .west = true) : bonus 138 p ≤ bonus 137 p := by
  have certified := compare5549 p (guard555 p guard)
  simpa only [at138, at137, Int.zero_add] using certified
theorem check555 (p : Pattern) : (!walkGuard soko3_2.board support p 138 137 .west || decide (bonus 138 p ≤ bonus 137 p)) = true :=
  check_of_implication _ _ (bound555 p)
theorem guard556 (p : Pattern) (guard : pushGuard support p 138 137 136 136 = true) : d857 p = 1 := by
  change (!(p 138) && (!false || false) && !false && (!false || false)) = true at guard
  cases h138 : p 138
  all_goals simp [d0, d1, d857, h138] at guard ⊢
theorem bound556 (p : Pattern) (guard : pushGuard support p 138 137 136 136 = true) : bonus 138 p ≤ 1 + Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.boulder 137 + bonus 137 (change p 137 (some 136)) := by
  have certified := compare5549 p (guard556 p guard)
  change d455 p ≤ (0 : Int) + d134 (change p 137 (some 136))
  have normalized := agree134 _ _ (change_representative support p 137 (some 136) 10000 dummy_outside)
  rw [normalized]
  change d455 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check556 (p : Pattern) : (!pushGuard support p 138 137 136 136 || decide (bonus 138 p ≤ 1 + Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.boulder 137 + bonus 137 (change p 137 (some 136)))) = true :=
  check_of_implication _ _ (bound556 p)
theorem guard557 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 113 .northEast = true) : d1126 p = 1 := by
  change (!(p 138) && !(p 113) && !(true && (p 112) && (p 139))) = true at guard
  cases h112 : p 112 <;> cases h113 : p 113 <;> cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d857, d1088, d1092, d1122, d1125, d1126, h112, h113, h138, h139] at guard ⊢
theorem bound557 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 113 .northEast = true) : bonus 138 p ≤ bonus 113 p := by
  have certified := compare5612 p (guard557 p guard)
  simpa only [at138, at113, Int.zero_add] using certified
theorem check557 (p : Pattern) : (!walkGuard soko3_2.board support p 138 113 .northEast || decide (bonus 138 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound557 p)
theorem guard558 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 165 .southEast = true) : d1092 p = 1 := by
  change (!(p 138) && !false && !(true && true && (p 139))) = true at guard
  cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1092, h138, h139] at guard ⊢
theorem bound558 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 165 .southEast = true) : bonus 138 p ≤ bonus 165 p := by
  have certified := compare5682 p (guard558 p guard)
  simpa only [at138, at165, Int.zero_add] using certified
theorem check558 (p : Pattern) : (!walkGuard soko3_2.board support p 138 165 .southEast || decide (bonus 138 p ≤ bonus 165 p)) = true :=
  check_of_implication _ _ (bound558 p)
theorem guard559 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 163 .southWest = true) : d857 p = 1 := by
  change (!(p 138) && !false && !(true && true && false)) = true at guard
  cases h138 : p 138
  all_goals simp [d0, d1, d857, h138] at guard ⊢
theorem bound559 (p : Pattern) (guard : walkGuard soko3_2.board support p 138 163 .southWest = true) : bonus 138 p ≤ bonus 163 p := by
  have certified := compare5549 p (guard559 p guard)
  simpa only [at138, at163, Int.zero_add] using certified
theorem check559 (p : Pattern) : (!walkGuard soko3_2.board support p 138 163 .southWest || decide (bonus 138 p ≤ bonus 163 p)) = true :=
  check_of_implication _ _ (bound559 p)
theorem guard560 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 113 .north = true) : d1095 p = 1 := by
  change (!(p 139) && !(p 113) && !false) = true at guard
  cases h113 : p 113 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1095, h113, h139] at guard ⊢
theorem bound560 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 113 .north = true) : bonus 139 p ≤ bonus 113 p := by
  have certified := compare5812 p (guard560 p guard)
  simpa only [at139, at113, Int.zero_add] using certified
theorem check560 (p : Pattern) : (!walkGuard soko3_2.board support p 139 113 .north || decide (bonus 139 p ≤ bonus 113 p)) = true :=
  check_of_implication _ _ (bound560 p)
theorem guard561 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 165 .south = true) : d1088 p = 1 := by
  change (!(p 139) && !false && !false) = true at guard
  cases h139 : p 139
  all_goals simp [d0, d1, d1088, h139] at guard ⊢
theorem bound561 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 165 .south = true) : bonus 139 p ≤ bonus 165 p := by
  have certified := compare5891 p (guard561 p guard)
  simpa only [at139, at165, Int.zero_add] using certified
theorem check561 (p : Pattern) : (!walkGuard soko3_2.board support p 139 165 .south || decide (bonus 139 p ≤ bonus 165 p)) = true :=
  check_of_implication _ _ (bound561 p)
theorem guard562 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 138 .west = true) : d1092 p = 1 := by
  change (!(p 139) && !(p 138) && !false) = true at guard
  cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1092, h138, h139] at guard ⊢
theorem bound562 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 138 .west = true) : bonus 139 p ≤ bonus 138 p := by
  have certified := compare5993 p (guard562 p guard)
  simpa only [at139, at138, Int.zero_add] using certified
theorem check562 (p : Pattern) : (!walkGuard soko3_2.board support p 139 138 .west || decide (bonus 139 p ≤ bonus 138 p)) = true :=
  check_of_implication _ _ (bound562 p)
theorem guard563 (p : Pattern) (guard : pushGuard support p 139 138 137 137 = true) : d1365 p = 1 := by
  change (!(p 139) && (!true || (p 138)) && !false && (!false || false)) = true at guard
  cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1365, h138, h139] at guard ⊢
theorem bound563 (p : Pattern) (guard : pushGuard support p 139 138 137 137 = true) : bonus 139 p ≤ 1 + Generated.soko3_2Potential.boulder 137 - Generated.soko3_2Potential.boulder 138 + bonus 138 (change p 138 (some 137)) := by
  have certified := compare6112 p (guard563 p guard)
  change d537 p ≤ (0 : Int) + d455 (change p 138 (some 137))
  have normalized := agree455 _ _ (change_representative support p 138 (some 137) 10000 dummy_outside)
  rw [normalized]
  change d537 p ≤ (0 : Int) + d455 (change p 138 none)
  rw [sub2585]
  exact certified
theorem check563 (p : Pattern) : (!pushGuard support p 139 138 137 137 || decide (bonus 139 p ≤ 1 + Generated.soko3_2Potential.boulder 137 - Generated.soko3_2Potential.boulder 138 + bonus 138 (change p 138 (some 137)))) = true :=
  check_of_implication _ _ (bound563 p)
theorem guard564 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 114 .northEast = true) : d1095 p = 1 := by
  change (!(p 139) && !false && !(true && (p 113) && true)) = true at guard
  cases h113 : p 113 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1095, h113, h139] at guard ⊢
theorem bound564 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 114 .northEast = true) : bonus 139 p ≤ bonus 114 p := by
  have certified := compare6154 p (guard564 p guard)
  simpa only [at139, at114, Int.zero_add] using certified
theorem check564 (p : Pattern) : (!walkGuard soko3_2.board support p 139 114 .northEast || decide (bonus 139 p ≤ bonus 114 p)) = true :=
  check_of_implication _ _ (bound564 p)
theorem guard565 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 112 .northWest = true) : d1094 p = 1 := by
  change (!(p 139) && !(p 112) && !(true && (p 113) && (p 138))) = true at guard
  cases h112 : p 112 <;> cases h113 : p 113 <;> cases h138 : p 138 <;> cases h139 : p 139
  all_goals simp [d0, d1, d1088, d1092, d1093, d1094, h112, h113, h138, h139] at guard ⊢
theorem bound565 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 112 .northWest = true) : bonus 139 p ≤ bonus 112 p := by
  have certified := compare6239 p (guard565 p guard)
  simpa only [at139, at112, Int.zero_add] using certified
theorem check565 (p : Pattern) : (!walkGuard soko3_2.board support p 139 112 .northWest || decide (bonus 139 p ≤ bonus 112 p)) = true :=
  check_of_implication _ _ (bound565 p)
theorem guard566 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 166 .southEast = true) : d1088 p = 1 := by
  change (!(p 139) && !false && !(true && false && true)) = true at guard
  cases h139 : p 139
  all_goals simp [d0, d1, d1088, h139] at guard ⊢
theorem bound566 (p : Pattern) (guard : walkGuard soko3_2.board support p 139 166 .southEast = true) : bonus 139 p ≤ bonus 166 p := by
  have certified := compare5891 p (guard566 p guard)
  simpa only [at139, at166, Int.zero_add] using certified
theorem check566 (p : Pattern) : (!walkGuard soko3_2.board support p 139 166 .southEast || decide (bonus 139 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound566 p)
theorem guard567 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 120 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound567 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 120 .north = true) : bonus 146 p ≤ bonus 120 p := by
  have certified := compare103 p (guard567 p guard)
  simpa only [at146, at120, Int.zero_add] using certified
theorem check567 (p : Pattern) : (!walkGuard soko3_2.board support p 146 120 .north || decide (bonus 146 p ≤ bonus 120 p)) = true :=
  check_of_implication _ _ (bound567 p)
theorem guard568 (p : Pattern) (guard : pushGuard support p 146 120 94 94 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound568 (p : Pattern) (guard : pushGuard support p 146 120 94 94 = true) : bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder 94 - Generated.soko3_2Potential.boulder 120 + bonus 120 (change p 120 (some 94)) := by
  have certified := compare37 p (guard568 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 120 (some 94))
  have normalized := agree0 _ _ (change_representative support p 120 (some 94) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check568 (p : Pattern) : (!pushGuard support p 146 120 94 94 || decide (bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder 94 - Generated.soko3_2Potential.boulder 120 + bonus 120 (change p 120 (some 94)))) = true :=
  check_of_implication _ _ (bound568 p)
theorem guard569 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 172 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound569 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 172 .south = true) : bonus 146 p ≤ bonus 172 p := by
  have certified := compare103 p (guard569 p guard)
  simpa only [at146, at172, Int.zero_add] using certified
theorem check569 (p : Pattern) : (!walkGuard soko3_2.board support p 146 172 .south || decide (bonus 146 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound569 p)
theorem guard570 (p : Pattern) (guard : pushGuard support p 146 172 198 198 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound570 (p : Pattern) (guard : pushGuard support p 146 172 198 198 = true) : bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder 198 - Generated.soko3_2Potential.boulder 172 + bonus 172 (change p 172 (some 198)) := by
  have certified := compare37 p (guard570 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 172 (some 198))
  have normalized := agree0 _ _ (change_representative support p 172 (some 198) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check570 (p : Pattern) : (!pushGuard support p 146 172 198 198 || decide (bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder 198 - Generated.soko3_2Potential.boulder 172 + bonus 172 (change p 172 (some 198)))) = true :=
  check_of_implication _ _ (bound570 p)
theorem guard571 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 147 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound571 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 147 .east = true) : bonus 146 p ≤ bonus 147 p := by
  have certified := compare103 p (guard571 p guard)
  simpa only [at146, at147, Int.zero_add] using certified
theorem check571 (p : Pattern) : (!walkGuard soko3_2.board support p 146 147 .east || decide (bonus 146 p ≤ bonus 147 p)) = true :=
  check_of_implication _ _ (bound571 p)
theorem guard572 (p : Pattern) (guard : pushGuard support p 146 147 148 148 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound572 (p : Pattern) (guard : pushGuard support p 146 147 148 148 = true) : bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some 148)) := by
  have certified := compare37 p (guard572 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 147 (some 148))
  have normalized := agree0 _ _ (change_representative support p 147 (some 148) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check572 (p : Pattern) : (!pushGuard support p 146 147 148 148 || decide (bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some 148)))) = true :=
  check_of_implication _ _ (bound572 p)
theorem guard573 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 121 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound573 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 121 .northEast = true) : bonus 146 p ≤ bonus 121 p := by
  have certified := compare103 p (guard573 p guard)
  simpa only [at146, at121, Int.zero_add] using certified
theorem check573 (p : Pattern) : (!walkGuard soko3_2.board support p 146 121 .northEast || decide (bonus 146 p ≤ bonus 121 p)) = true :=
  check_of_implication _ _ (bound573 p)
theorem guard574 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 173 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound574 (p : Pattern) (guard : walkGuard soko3_2.board support p 146 173 .southEast = true) : bonus 146 p ≤ bonus 173 p := by
  have certified := compare103 p (guard574 p guard)
  simpa only [at146, at173, Int.zero_add] using certified
theorem check574 (p : Pattern) : (!walkGuard soko3_2.board support p 146 173 .southEast || decide (bonus 146 p ≤ bonus 173 p)) = true :=
  check_of_implication _ _ (bound574 p)
theorem guard575 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 121 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound575 (p : Pattern) (guard : walkGuard soko3_2.board support p 147 121 .north = true) : bonus 147 p ≤ bonus 121 p := by
  have certified := compare103 p (guard575 p guard)
  simpa only [at147, at121, Int.zero_add] using certified
theorem check575 (p : Pattern) : (!walkGuard soko3_2.board support p 147 121 .north || decide (bonus 147 p ≤ bonus 121 p)) = true :=
  check_of_implication _ _ (bound575 p)
end NetHack.Sokoban32Refined
