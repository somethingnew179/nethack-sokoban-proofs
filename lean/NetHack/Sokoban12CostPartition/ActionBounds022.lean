import NetHack.Sokoban12CostPartition.ActionBounds021
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard528 (p : Pattern) (guard : pushGuard support p 216 190 164 164 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound528 (p : Pattern) (guard : pushGuard support p 216 190 164 164 = true) : bonus 216 p ≤ 1 + Generated.soko1_2Potential.boulder 164 - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some 164)) := by
  have certified := compare5792 p (guard528 p guard)
  change d258 p ≤ (6 : Int) + d258 (change p 190 (some 164))
  have normalized := agree258 _ _ (change_representative support p 190 (some 164) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (6 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check528 (p : Pattern) : (!pushGuard support p 216 190 164 164 || decide (bonus 216 p ≤ 1 + Generated.soko1_2Potential.boulder 164 - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some 164)))) = true :=
  check_of_implication _ _ (bound528 p)
theorem guard529 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 242 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound529 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 242 .south = true) : bonus 216 p ≤ bonus 242 p := by
  have certified := compare897 p (guard529 p guard)
  simpa only [at216, at242, Int.zero_add] using certified
theorem check529 (p : Pattern) : (!walkGuard soko1_2.board support p 216 242 .south || decide (bonus 216 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound529 p)
theorem guard530 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 215 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound530 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 215 .west = true) : bonus 216 p ≤ bonus 215 p := by
  have certified := compare897 p (guard530 p guard)
  simpa only [at216, at215, Int.zero_add] using certified
theorem check530 (p : Pattern) : (!walkGuard soko1_2.board support p 216 215 .west || decide (bonus 216 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound530 p)
theorem guard531 (p : Pattern) (guard : pushGuard support p 216 215 214 214 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound531 (p : Pattern) (guard : pushGuard support p 216 215 214 214 = true) : bonus 216 p ≤ 1 + Generated.soko1_2Potential.boulder 214 - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some 214)) := by
  have certified := compare897 p (guard531 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 215 (some 214))
  have normalized := agree258 _ _ (change_representative support p 215 (some 214) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check531 (p : Pattern) : (!pushGuard support p 216 215 214 214 || decide (bonus 216 p ≤ 1 + Generated.soko1_2Potential.boulder 214 - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some 214)))) = true :=
  check_of_implication _ _ (bound531 p)
theorem guard532 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 191 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound532 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 191 .northEast = true) : bonus 216 p ≤ bonus 191 p := by
  have certified := compare897 p (guard532 p guard)
  simpa only [at216, at191, Int.zero_add] using certified
theorem check532 (p : Pattern) : (!walkGuard soko1_2.board support p 216 191 .northEast || decide (bonus 216 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound532 p)
theorem guard533 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 189 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound533 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 189 .northWest = true) : bonus 216 p ≤ bonus 189 p := by
  have certified := compare897 p (guard533 p guard)
  simpa only [at216, at189, Int.zero_add] using certified
theorem check533 (p : Pattern) : (!walkGuard soko1_2.board support p 216 189 .northWest || decide (bonus 216 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound533 p)
theorem guard534 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 241 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound534 (p : Pattern) (guard : walkGuard soko1_2.board support p 216 241 .southWest = true) : bonus 216 p ≤ bonus 241 p := by
  have certified := compare897 p (guard534 p guard)
  simpa only [at216, at241, Int.zero_add] using certified
theorem check534 (p : Pattern) : (!walkGuard soko1_2.board support p 216 241 .southWest || decide (bonus 216 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound534 p)
theorem guard535 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 192 .north = true) : d854 p = 1 := by
  change (!false && !(p 192) && !false) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound535 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 192 .north = true) : bonus 218 p ≤ bonus 192 p := by
  have certified := compare2639 p (guard535 p guard)
  simpa only [at218, at192, Int.zero_add] using certified
theorem check535 (p : Pattern) : (!walkGuard soko1_2.board support p 218 192 .north || decide (bonus 218 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound535 p)
theorem guard536 (p : Pattern) (guard : pushGuard support p 218 192 166 166 = true) : d853 p = 1 := by
  change (!false && (!true || (p 192)) && !false && (!false || false)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d853, h192] at guard ⊢
theorem bound536 (p : Pattern) (guard : pushGuard support p 218 192 166 166 = true) : bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder 166 - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some 166)) := by
  have certified := compare2716 p (guard536 p guard)
  change d258 p ≤ (2 : Int) + d586 (change p 192 (some 166))
  have normalized := agree586 _ _ (change_representative support p 192 (some 166) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d586 (change p 192 none)
  rw [sub1623]
  exact certified
theorem check536 (p : Pattern) : (!pushGuard support p 218 192 166 166 || decide (bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder 166 - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some 166)))) = true :=
  check_of_implication _ _ (bound536 p)
theorem guard537 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 244 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound537 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 244 .south = true) : bonus 218 p ≤ bonus 244 p := by
  have certified := compare897 p (guard537 p guard)
  simpa only [at218, at244, Int.zero_add] using certified
theorem check537 (p : Pattern) : (!walkGuard soko1_2.board support p 218 244 .south || decide (bonus 218 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound537 p)
theorem guard538 (p : Pattern) (guard : pushGuard support p 218 244 270 270 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound538 (p : Pattern) (guard : pushGuard support p 218 244 270 270 = true) : bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder 270 - Generated.soko1_2Potential.boulder 244 + bonus 244 (change p 244 (some 270)) := by
  have certified := compare2570 p (guard538 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 244 (some 270))
  have normalized := agree258 _ _ (change_representative support p 244 (some 270) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check538 (p : Pattern) : (!pushGuard support p 218 244 270 270 || decide (bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder 270 - Generated.soko1_2Potential.boulder 244 + bonus 244 (change p 244 (some 270)))) = true :=
  check_of_implication _ _ (bound538 p)
theorem guard539 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 219 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound539 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 219 .east = true) : bonus 218 p ≤ bonus 219 p := by
  have certified := compare897 p (guard539 p guard)
  simpa only [at218, at219, Int.zero_add] using certified
theorem check539 (p : Pattern) : (!walkGuard soko1_2.board support p 218 219 .east || decide (bonus 218 p ≤ bonus 219 p)) = true :=
  check_of_implication _ _ (bound539 p)
theorem guard540 (p : Pattern) (guard : pushGuard support p 218 219 220 220 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound540 (p : Pattern) (guard : pushGuard support p 218 219 220 220 = true) : bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder 220 - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some 220)) := by
  have certified := compare2570 p (guard540 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 219 (some 220))
  have normalized := agree258 _ _ (change_representative support p 219 (some 220) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check540 (p : Pattern) : (!pushGuard support p 218 219 220 220 || decide (bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder 220 - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some 220)))) = true :=
  check_of_implication _ _ (bound540 p)
theorem guard541 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 193 .northEast = true) : d917 p = 1 := by
  change (!false && !(p 193) && !(true && (p 192) && false)) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d917, h192, h193] at guard ⊢
theorem bound541 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 193 .northEast = true) : bonus 218 p ≤ bonus 193 p := by
  have certified := compare2879 p (guard541 p guard)
  simpa only [at218, at193, Int.zero_add] using certified
theorem check541 (p : Pattern) : (!walkGuard soko1_2.board support p 218 193 .northEast || decide (bonus 218 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound541 p)
theorem guard542 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 191 .northWest = true) : d854 p = 1 := by
  change (!false && !false && !(true && (p 192) && true)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound542 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 191 .northWest = true) : bonus 218 p ≤ bonus 191 p := by
  have certified := compare2880 p (guard542 p guard)
  simpa only [at218, at191, Int.zero_add] using certified
theorem check542 (p : Pattern) : (!walkGuard soko1_2.board support p 218 191 .northWest || decide (bonus 218 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound542 p)
theorem guard543 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 245 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound543 (p : Pattern) (guard : walkGuard soko1_2.board support p 218 245 .southEast = true) : bonus 218 p ≤ bonus 245 p := by
  have certified := compare897 p (guard543 p guard)
  simpa only [at218, at245, Int.zero_add] using certified
theorem check543 (p : Pattern) : (!walkGuard soko1_2.board support p 218 245 .southEast || decide (bonus 218 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound543 p)
theorem guard544 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 193 .north = true) : d917 p = 1 := by
  change (!false && !(p 193) && !false) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound544 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 193 .north = true) : bonus 219 p ≤ bonus 193 p := by
  have certified := compare2879 p (guard544 p guard)
  simpa only [at219, at193, Int.zero_add] using certified
theorem check544 (p : Pattern) : (!walkGuard soko1_2.board support p 219 193 .north || decide (bonus 219 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound544 p)
theorem guard545 (p : Pattern) (guard : pushGuard support p 219 193 167 167 = true) : d916 p = 1 := by
  change (!false && (!true || (p 193)) && !false && (!false || false)) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d916, h193] at guard ⊢
theorem bound545 (p : Pattern) (guard : pushGuard support p 219 193 167 167 = true) : bonus 219 p ≤ 1 + Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some 167)) := by
  have certified := compare2953 p (guard545 p guard)
  change d258 p ≤ (2 : Int) + d658 (change p 193 (some 167))
  have normalized := agree658 _ _ (change_representative support p 193 (some 167) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d658 (change p 193 none)
  rw [sub1764]
  exact certified
theorem check545 (p : Pattern) : (!pushGuard support p 219 193 167 167 || decide (bonus 219 p ≤ 1 + Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some 167)))) = true :=
  check_of_implication _ _ (bound545 p)
theorem guard546 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 245 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound546 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 245 .south = true) : bonus 219 p ≤ bonus 245 p := by
  have certified := compare897 p (guard546 p guard)
  simpa only [at219, at245, Int.zero_add] using certified
theorem check546 (p : Pattern) : (!walkGuard soko1_2.board support p 219 245 .south || decide (bonus 219 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound546 p)
theorem guard547 (p : Pattern) (guard : pushGuard support p 219 245 271 271 = true) : d1233 p = 1 := by
  change (!false && (!false || false) && !(p 271) && (!(p 271) || false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound547 (p : Pattern) (guard : pushGuard support p 219 245 271 271 = true) : bonus 219 p ≤ 1 + Generated.soko1_2Potential.boulder 271 - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some 271)) := by
  have certified := compare5860 p (guard547 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 245 (some 271))
  have normalized := agree258 _ _ (change_representative support p 245 (some 271) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 (some 271))
  rw [sub2564]
  exact certified
theorem check547 (p : Pattern) : (!pushGuard support p 219 245 271 271 || decide (bonus 219 p ≤ 1 + Generated.soko1_2Potential.boulder 271 - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some 271)))) = true :=
  check_of_implication _ _ (bound547 p)
theorem guard548 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 220 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound548 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 220 .east = true) : bonus 219 p ≤ bonus 220 p := by
  have certified := compare897 p (guard548 p guard)
  simpa only [at219, at220, Int.zero_add] using certified
theorem check548 (p : Pattern) : (!walkGuard soko1_2.board support p 219 220 .east || decide (bonus 219 p ≤ bonus 220 p)) = true :=
  check_of_implication _ _ (bound548 p)
theorem guard549 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 218 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound549 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 218 .west = true) : bonus 219 p ≤ bonus 218 p := by
  have certified := compare897 p (guard549 p guard)
  simpa only [at219, at218, Int.zero_add] using certified
theorem check549 (p : Pattern) : (!walkGuard soko1_2.board support p 219 218 .west || decide (bonus 219 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound549 p)
theorem guard550 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 194 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 193) && false)) = true at guard
  cases h193 : p 193
  all_goals simp [d1, h193] at guard ⊢
theorem bound550 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 194 .northEast = true) : bonus 219 p ≤ bonus 194 p := by
  have certified := compare897 p (guard550 p guard)
  simpa only [at219, at194, Int.zero_add] using certified
theorem check550 (p : Pattern) : (!walkGuard soko1_2.board support p 219 194 .northEast || decide (bonus 219 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound550 p)
theorem guard551 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 192 .northWest = true) : d854 p = 1 := by
  change (!false && !(p 192) && !(true && (p 193) && false)) = true at guard
  cases h192 : p 192 <;> cases h193 : p 193
  all_goals simp [d0, d1, d854, h192, h193] at guard ⊢
theorem bound551 (p : Pattern) (guard : walkGuard soko1_2.board support p 219 192 .northWest = true) : bonus 219 p ≤ bonus 192 p := by
  have certified := compare2639 p (guard551 p guard)
  simpa only [at219, at192, Int.zero_add] using certified
theorem check551 (p : Pattern) : (!walkGuard soko1_2.board support p 219 192 .northWest || decide (bonus 219 p ≤ bonus 192 p)) = true :=
  check_of_implication _ _ (bound551 p)
end NetHack.Sokoban12CostPartition
