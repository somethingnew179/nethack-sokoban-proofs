import NetHack.Sokoban12CostPartition.ActionBounds017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard432 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 166 .northEast = true) : d854 p = 1 := by
  change (!false && !false && !(true && true && (p 192))) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound432 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 166 .northEast = true) : bonus 191 p ≤ bonus 166 p := by
  have certified := compare2880 p (guard432 p guard)
  simpa only [at191, at166, Int.zero_add] using certified
theorem check432 (p : Pattern) : (!walkGuard soko1_2.board support p 191 166 .northEast || decide (bonus 191 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound432 p)
theorem guard433 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 164 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound433 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 164 .northWest = true) : bonus 191 p ≤ bonus 164 p := by
  have certified := compare897 p (guard433 p guard)
  simpa only [at191, at164, Int.zero_add] using certified
theorem check433 (p : Pattern) : (!walkGuard soko1_2.board support p 191 164 .northWest || decide (bonus 191 p ≤ bonus 164 p)) = true :=
  check_of_implication _ _ (bound433 p)
theorem guard434 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 218 .southEast = true) : d854 p = 1 := by
  change (!false && !false && !(true && true && (p 192))) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound434 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 218 .southEast = true) : bonus 191 p ≤ bonus 218 p := by
  have certified := compare2880 p (guard434 p guard)
  simpa only [at191, at218, Int.zero_add] using certified
theorem check434 (p : Pattern) : (!walkGuard soko1_2.board support p 191 218 .southEast || decide (bonus 191 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound434 p)
theorem guard435 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 216 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound435 (p : Pattern) (guard : walkGuard soko1_2.board support p 191 216 .southWest = true) : bonus 191 p ≤ bonus 216 p := by
  have certified := compare897 p (guard435 p guard)
  simpa only [at191, at216, Int.zero_add] using certified
theorem check435 (p : Pattern) : (!walkGuard soko1_2.board support p 191 216 .southWest || decide (bonus 191 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound435 p)
theorem guard436 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 166 .north = true) : d854 p = 1 := by
  change (!(p 192) && !false && !false) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound436 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 166 .north = true) : bonus 192 p ≤ bonus 166 p := by
  have certified := compare4656 p (guard436 p guard)
  simpa only [at192, at166, Int.zero_add] using certified
theorem check436 (p : Pattern) : (!walkGuard soko1_2.board support p 192 166 .north || decide (bonus 192 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound436 p)
theorem guard437 (p : Pattern) (guard : pushGuard support p 192 166 140 140 = true) : d854 p = 1 := by
  change (!(p 192) && (!false || false) && !false && (!false || false)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound437 (p : Pattern) (guard : pushGuard support p 192 166 140 140 = true) : bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder 140 - Generated.soko1_2Potential.boulder 166 + bonus 166 (change p 166 (some 140)) := by
  have certified := compare4729 p (guard437 p guard)
  change d586 p ≤ (3 : Int) + d258 (change p 166 (some 140))
  have normalized := agree258 _ _ (change_representative support p 166 (some 140) 10000 dummy_outside)
  rw [normalized]
  change d586 p ≤ (3 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check437 (p : Pattern) : (!pushGuard support p 192 166 140 140 || decide (bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder 140 - Generated.soko1_2Potential.boulder 166 + bonus 166 (change p 166 (some 140)))) = true :=
  check_of_implication _ _ (bound437 p)
theorem guard438 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 218 .south = true) : d854 p = 1 := by
  change (!(p 192) && !false && !false) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound438 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 218 .south = true) : bonus 192 p ≤ bonus 218 p := by
  have certified := compare4656 p (guard438 p guard)
  simpa only [at192, at218, Int.zero_add] using certified
theorem check438 (p : Pattern) : (!walkGuard soko1_2.board support p 192 218 .south || decide (bonus 192 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound438 p)
theorem guard439 (p : Pattern) (guard : pushGuard support p 192 218 244 244 = true) : d854 p = 1 := by
  change (!(p 192) && (!false || false) && !false && (!false || false)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound439 (p : Pattern) (guard : pushGuard support p 192 218 244 244 = true) : bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder 244 - Generated.soko1_2Potential.boulder 218 + bonus 218 (change p 218 (some 244)) := by
  have certified := compare4798 p (guard439 p guard)
  change d586 p ≤ (2 : Int) + d258 (change p 218 (some 244))
  have normalized := agree258 _ _ (change_representative support p 218 (some 244) 10000 dummy_outside)
  rw [normalized]
  change d586 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check439 (p : Pattern) : (!pushGuard support p 192 218 244 244 || decide (bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder 244 - Generated.soko1_2Potential.boulder 218 + bonus 218 (change p 218 (some 244)))) = true :=
  check_of_implication _ _ (bound439 p)
theorem guard440 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 193 .east = true) : d1175 p = 1 := by
  change (!(p 192) && !(p 193) && !false) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d1175, h192, h193] at guard ⊢
theorem bound440 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 193 .east = true) : bonus 192 p ≤ bonus 193 p := by
  have certified := compare4878 p (guard440 p guard)
  simpa only [at192, at193, Int.zero_add] using certified
theorem check440 (p : Pattern) : (!walkGuard soko1_2.board support p 192 193 .east || decide (bonus 192 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound440 p)
theorem guard441 (p : Pattern) (guard : pushGuard support p 192 193 194 194 = true) : d1176 p = 1 := by
  change (!(p 192) && (!true || (p 193)) && !false && (!false || false)) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d916, d1176, h192, h193] at guard ⊢
theorem bound441 (p : Pattern) (guard : pushGuard support p 192 193 194 194 = true) : bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder 194 - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some 194)) := by
  have certified := compare4951 p (guard441 p guard)
  change d586 p ≤ (3 : Int) + d658 (change p 193 (some 194))
  have normalized := agree658 _ _ (change_representative support p 193 (some 194) 10000 dummy_outside)
  rw [normalized]
  change d586 p ≤ (3 : Int) + d658 (change p 193 none)
  rw [sub1764]
  exact certified
theorem check441 (p : Pattern) : (!pushGuard support p 192 193 194 194 || decide (bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder 194 - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some 194)))) = true :=
  check_of_implication _ _ (bound441 p)
theorem guard442 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 191 .west = true) : d854 p = 1 := by
  change (!(p 192) && !false && !false) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound442 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 191 .west = true) : bonus 192 p ≤ bonus 191 p := by
  have certified := compare4656 p (guard442 p guard)
  simpa only [at192, at191, Int.zero_add] using certified
theorem check442 (p : Pattern) : (!walkGuard soko1_2.board support p 192 191 .west || decide (bonus 192 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound442 p)
theorem guard443 (p : Pattern) (guard : pushGuard support p 192 191 190 190 = true) : d854 p = 1 := by
  change (!(p 192) && (!false || false) && !false && (!false || false)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound443 (p : Pattern) (guard : pushGuard support p 192 191 190 190 = true) : bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder 190 - Generated.soko1_2Potential.boulder 191 + bonus 191 (change p 191 (some 190)) := by
  have certified := compare4656 p (guard443 p guard)
  change d586 p ≤ (0 : Int) + d258 (change p 191 (some 190))
  have normalized := agree258 _ _ (change_representative support p 191 (some 190) 10000 dummy_outside)
  rw [normalized]
  change d586 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check443 (p : Pattern) : (!pushGuard support p 192 191 190 190 || decide (bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder 190 - Generated.soko1_2Potential.boulder 191 + bonus 191 (change p 191 (some 190)))) = true :=
  check_of_implication _ _ (bound443 p)
theorem guard444 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 167 .northEast = true) : d854 p = 1 := by
  change (!(p 192) && !false && !(true && false && (p 193))) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d854, h192, h193] at guard ⊢
theorem bound444 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 167 .northEast = true) : bonus 192 p ≤ bonus 167 p := by
  have certified := compare4656 p (guard444 p guard)
  simpa only [at192, at167, Int.zero_add] using certified
theorem check444 (p : Pattern) : (!walkGuard soko1_2.board support p 192 167 .northEast || decide (bonus 192 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound444 p)
theorem guard445 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 219 .southEast = true) : d854 p = 1 := by
  change (!(p 192) && !false && !(true && false && (p 193))) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d854, h192, h193] at guard ⊢
theorem bound445 (p : Pattern) (guard : walkGuard soko1_2.board support p 192 219 .southEast = true) : bonus 192 p ≤ bonus 219 p := by
  have certified := compare4656 p (guard445 p guard)
  simpa only [at192, at219, Int.zero_add] using certified
theorem check445 (p : Pattern) : (!walkGuard soko1_2.board support p 192 219 .southEast || decide (bonus 192 p ≤ bonus 219 p)) = true :=
  check_of_implication _ _ (bound445 p)
theorem guard446 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 167 .north = true) : d917 p = 1 := by
  change (!(p 193) && !false && !false) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound446 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 167 .north = true) : bonus 193 p ≤ bonus 167 p := by
  have certified := compare5047 p (guard446 p guard)
  simpa only [at193, at167, Int.zero_add] using certified
theorem check446 (p : Pattern) : (!walkGuard soko1_2.board support p 193 167 .north || decide (bonus 193 p ≤ bonus 167 p)) = true :=
  check_of_implication _ _ (bound446 p)
theorem guard447 (p : Pattern) (guard : pushGuard support p 193 167 141 141 = true) : d918 p = 1 := by
  change (!(p 193) && (!false || false) && !(p 141) && (!(p 141) || false)) = true at guard
  cases h141 : p 141 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d918, h141, h193] at guard ⊢
theorem bound447 (p : Pattern) (guard : pushGuard support p 193 167 141 141 = true) : bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder 141 - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some 141)) := by
  have certified := compare5116 p (guard447 p guard)
  change d658 p ≤ (2 : Int) + d258 (change p 167 (some 141))
  have normalized := agree258 _ _ (change_representative support p 167 (some 141) 10000 dummy_outside)
  rw [normalized]
  change d658 p ≤ (2 : Int) + d258 (change p 10000 (some 141))
  rw [sub2190]
  exact certified
theorem check447 (p : Pattern) : (!pushGuard support p 193 167 141 141 || decide (bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder 141 - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some 141)))) = true :=
  check_of_implication _ _ (bound447 p)
theorem guard448 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 219 .south = true) : d917 p = 1 := by
  change (!(p 193) && !false && !false) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound448 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 219 .south = true) : bonus 193 p ≤ bonus 219 p := by
  have certified := compare5047 p (guard448 p guard)
  simpa only [at193, at219, Int.zero_add] using certified
theorem check448 (p : Pattern) : (!walkGuard soko1_2.board support p 193 219 .south || decide (bonus 193 p ≤ bonus 219 p)) = true :=
  check_of_implication _ _ (bound448 p)
theorem guard449 (p : Pattern) (guard : pushGuard support p 193 219 245 245 = true) : d917 p = 1 := by
  change (!(p 193) && (!false || false) && !false && (!false || false)) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound449 (p : Pattern) (guard : pushGuard support p 193 219 245 245 = true) : bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder 245 - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some 245)) := by
  have certified := compare5196 p (guard449 p guard)
  change d658 p ≤ (2 : Int) + d258 (change p 219 (some 245))
  have normalized := agree258 _ _ (change_representative support p 219 (some 245) 10000 dummy_outside)
  rw [normalized]
  change d658 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check449 (p : Pattern) : (!pushGuard support p 193 219 245 245 || decide (bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder 245 - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some 245)))) = true :=
  check_of_implication _ _ (bound449 p)
theorem guard450 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 194 .east = true) : d917 p = 1 := by
  change (!(p 193) && !false && !false) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound450 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 194 .east = true) : bonus 193 p ≤ bonus 194 p := by
  have certified := compare5047 p (guard450 p guard)
  simpa only [at193, at194, Int.zero_add] using certified
theorem check450 (p : Pattern) : (!walkGuard soko1_2.board support p 193 194 .east || decide (bonus 193 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound450 p)
theorem guard451 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 192 .west = true) : d1175 p = 1 := by
  change (!(p 193) && !(p 192) && !false) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d1175, h192, h193] at guard ⊢
theorem bound451 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 192 .west = true) : bonus 193 p ≤ bonus 192 p := by
  have certified := compare5276 p (guard451 p guard)
  simpa only [at193, at192, Int.zero_add] using certified
theorem check451 (p : Pattern) : (!walkGuard soko1_2.board support p 193 192 .west || decide (bonus 193 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound451 p)
theorem guard452 (p : Pattern) (guard : pushGuard support p 193 192 191 191 = true) : d1174 p = 1 := by
  change (!(p 193) && (!true || (p 192)) && !false && (!false || false)) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d1174, h192, h193] at guard ⊢
theorem bound452 (p : Pattern) (guard : pushGuard support p 193 192 191 191 = true) : bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder 191 - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some 191)) := by
  have certified := compare5362 p (guard452 p guard)
  change d658 p ≤ (0 : Int) + d586 (change p 192 (some 191))
  have normalized := agree586 _ _ (change_representative support p 192 (some 191) 10000 dummy_outside)
  rw [normalized]
  change d658 p ≤ (0 : Int) + d586 (change p 192 none)
  rw [sub1623]
  exact certified
theorem check452 (p : Pattern) : (!pushGuard support p 193 192 191 191 || decide (bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder 191 - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some 191)))) = true :=
  check_of_implication _ _ (bound452 p)
theorem guard453 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 168 .northEast = true) : d1134 p = 1 := by
  change (!(p 193) && !(p 168) && !(true && false && false)) = true at guard
  cases h168 : p 168 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, d1134, h168, h193] at guard ⊢
theorem bound453 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 168 .northEast = true) : bonus 193 p ≤ bonus 168 p := by
  have certified := compare5430 p (guard453 p guard)
  simpa only [at193, at168, Int.zero_add] using certified
theorem check453 (p : Pattern) : (!walkGuard soko1_2.board support p 193 168 .northEast || decide (bonus 193 p ≤ bonus 168 p)) = true :=
  check_of_implication _ _ (bound453 p)
theorem guard454 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 166 .northWest = true) : d917 p = 1 := by
  change (!(p 193) && !false && !(true && false && (p 192))) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, h192, h193] at guard ⊢
theorem bound454 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 166 .northWest = true) : bonus 193 p ≤ bonus 166 p := by
  have certified := compare5047 p (guard454 p guard)
  simpa only [at193, at166, Int.zero_add] using certified
theorem check454 (p : Pattern) : (!walkGuard soko1_2.board support p 193 166 .northWest || decide (bonus 193 p ≤ bonus 166 p)) = true :=
  check_of_implication _ _ (bound454 p)
theorem guard455 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 220 .southEast = true) : d917 p = 1 := by
  change (!(p 193) && !false && !(true && false && false)) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound455 (p : Pattern) (guard : walkGuard soko1_2.board support p 193 220 .southEast = true) : bonus 193 p ≤ bonus 220 p := by
  have certified := compare5047 p (guard455 p guard)
  simpa only [at193, at220, Int.zero_add] using certified
theorem check455 (p : Pattern) : (!walkGuard soko1_2.board support p 193 220 .southEast || decide (bonus 193 p ≤ bonus 220 p)) = true :=
  check_of_implication _ _ (bound455 p)
end NetHack.Sokoban12CostPartition
