import NetHack.Sokoban12CostPartition.ActionBounds024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard600 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 238 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound600 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 238 .west = true) : bonus 239 p ≤ bonus 238 p := by
  have certified := compare897 p (guard600 p guard)
  simpa only [at239, at238, Int.zero_add] using certified
theorem check600 (p : Pattern) : (!walkGuard soko1_2.board support p 239 238 .west || decide (bonus 239 p ≤ bonus 238 p)) = true :=
  check_of_implication _ _ (bound600 p)
theorem guard601 (p : Pattern) (guard : pushGuard support p 239 238 237 237 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound601 (p : Pattern) (guard : pushGuard support p 239 238 237 237 = true) : bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some 237)) := by
  have certified := compare2570 p (guard601 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 238 (some 237))
  have normalized := agree258 _ _ (change_representative support p 238 (some 237) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check601 (p : Pattern) : (!pushGuard support p 239 238 237 237 || decide (bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some 237)))) = true :=
  check_of_implication _ _ (bound601 p)
theorem guard602 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 214 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound602 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 214 .northEast = true) : bonus 239 p ≤ bonus 214 p := by
  have certified := compare897 p (guard602 p guard)
  simpa only [at239, at214, Int.zero_add] using certified
theorem check602 (p : Pattern) : (!walkGuard soko1_2.board support p 239 214 .northEast || decide (bonus 239 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound602 p)
theorem guard603 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 212 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound603 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 212 .northWest = true) : bonus 239 p ≤ bonus 212 p := by
  have certified := compare897 p (guard603 p guard)
  simpa only [at239, at212, Int.zero_add] using certified
theorem check603 (p : Pattern) : (!walkGuard soko1_2.board support p 239 212 .northWest || decide (bonus 239 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound603 p)
theorem guard604 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 264 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound604 (p : Pattern) (guard : walkGuard soko1_2.board support p 239 264 .southWest = true) : bonus 239 p ≤ bonus 264 p := by
  have certified := compare897 p (guard604 p guard)
  simpa only [at239, at264, Int.zero_add] using certified
theorem check604 (p : Pattern) : (!walkGuard soko1_2.board support p 239 264 .southWest || decide (bonus 239 p ≤ bonus 264 p)) = true :=
  check_of_implication _ _ (bound604 p)
theorem guard605 (p : Pattern) (guard : walkGuard soko1_2.board support p 241 215 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound605 (p : Pattern) (guard : walkGuard soko1_2.board support p 241 215 .north = true) : bonus 241 p ≤ bonus 215 p := by
  have certified := compare897 p (guard605 p guard)
  simpa only [at241, at215, Int.zero_add] using certified
theorem check605 (p : Pattern) : (!walkGuard soko1_2.board support p 241 215 .north || decide (bonus 241 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound605 p)
theorem guard606 (p : Pattern) (guard : pushGuard support p 241 215 189 189 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound606 (p : Pattern) (guard : pushGuard support p 241 215 189 189 = true) : bonus 241 p ≤ 1 + Generated.soko1_2Potential.boulder 189 - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some 189)) := by
  have certified := compare2570 p (guard606 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 215 (some 189))
  have normalized := agree258 _ _ (change_representative support p 215 (some 189) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check606 (p : Pattern) : (!pushGuard support p 241 215 189 189 || decide (bonus 241 p ≤ 1 + Generated.soko1_2Potential.boulder 189 - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some 189)))) = true :=
  check_of_implication _ _ (bound606 p)
theorem guard607 (p : Pattern) (guard : walkGuard soko1_2.board support p 241 242 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound607 (p : Pattern) (guard : walkGuard soko1_2.board support p 241 242 .east = true) : bonus 241 p ≤ bonus 242 p := by
  have certified := compare897 p (guard607 p guard)
  simpa only [at241, at242, Int.zero_add] using certified
theorem check607 (p : Pattern) : (!walkGuard soko1_2.board support p 241 242 .east || decide (bonus 241 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound607 p)
theorem guard608 (p : Pattern) (guard : walkGuard soko1_2.board support p 241 216 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound608 (p : Pattern) (guard : walkGuard soko1_2.board support p 241 216 .northEast = true) : bonus 241 p ≤ bonus 216 p := by
  have certified := compare897 p (guard608 p guard)
  simpa only [at241, at216, Int.zero_add] using certified
theorem check608 (p : Pattern) : (!walkGuard soko1_2.board support p 241 216 .northEast || decide (bonus 241 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound608 p)
theorem guard609 (p : Pattern) (guard : walkGuard soko1_2.board support p 241 214 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound609 (p : Pattern) (guard : walkGuard soko1_2.board support p 241 214 .northWest = true) : bonus 241 p ≤ bonus 214 p := by
  have certified := compare897 p (guard609 p guard)
  simpa only [at241, at214, Int.zero_add] using certified
theorem check609 (p : Pattern) : (!walkGuard soko1_2.board support p 241 214 .northWest || decide (bonus 241 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound609 p)
theorem guard610 (p : Pattern) (guard : walkGuard soko1_2.board support p 242 216 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound610 (p : Pattern) (guard : walkGuard soko1_2.board support p 242 216 .north = true) : bonus 242 p ≤ bonus 216 p := by
  have certified := compare897 p (guard610 p guard)
  simpa only [at242, at216, Int.zero_add] using certified
theorem check610 (p : Pattern) : (!walkGuard soko1_2.board support p 242 216 .north || decide (bonus 242 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound610 p)
theorem guard611 (p : Pattern) (guard : pushGuard support p 242 216 190 190 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound611 (p : Pattern) (guard : pushGuard support p 242 216 190 190 = true) : bonus 242 p ≤ 1 + Generated.soko1_2Potential.boulder 190 - Generated.soko1_2Potential.boulder 216 + bonus 216 (change p 216 (some 190)) := by
  have certified := compare897 p (guard611 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 216 (some 190))
  have normalized := agree258 _ _ (change_representative support p 216 (some 190) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check611 (p : Pattern) : (!pushGuard support p 242 216 190 190 || decide (bonus 242 p ≤ 1 + Generated.soko1_2Potential.boulder 190 - Generated.soko1_2Potential.boulder 216 + bonus 216 (change p 216 (some 190)))) = true :=
  check_of_implication _ _ (bound611 p)
theorem guard612 (p : Pattern) (guard : walkGuard soko1_2.board support p 242 241 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound612 (p : Pattern) (guard : walkGuard soko1_2.board support p 242 241 .west = true) : bonus 242 p ≤ bonus 241 p := by
  have certified := compare897 p (guard612 p guard)
  simpa only [at242, at241, Int.zero_add] using certified
theorem check612 (p : Pattern) : (!walkGuard soko1_2.board support p 242 241 .west || decide (bonus 242 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound612 p)
theorem guard613 (p : Pattern) (guard : walkGuard soko1_2.board support p 242 215 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound613 (p : Pattern) (guard : walkGuard soko1_2.board support p 242 215 .northWest = true) : bonus 242 p ≤ bonus 215 p := by
  have certified := compare897 p (guard613 p guard)
  simpa only [at242, at215, Int.zero_add] using certified
theorem check613 (p : Pattern) : (!walkGuard soko1_2.board support p 242 215 .northWest || decide (bonus 242 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound613 p)
theorem guard614 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 218 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound614 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 218 .north = true) : bonus 244 p ≤ bonus 218 p := by
  have certified := compare897 p (guard614 p guard)
  simpa only [at244, at218, Int.zero_add] using certified
theorem check614 (p : Pattern) : (!walkGuard soko1_2.board support p 244 218 .north || decide (bonus 244 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound614 p)
theorem guard615 (p : Pattern) (guard : pushGuard support p 244 218 192 192 = true) : d854 p = 1 := by
  change (!false && (!false || false) && !(p 192) && (!(p 192) || false)) = true at guard
  cases h192 : p 192
  all_goals simp [d0, d1, d854, h192] at guard ⊢
theorem bound615 (p : Pattern) (guard : pushGuard support p 244 218 192 192 = true) : bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.boulder 218 + bonus 218 (change p 218 (some 192)) := by
  have certified := compare974 p (guard615 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 218 (some 192))
  have normalized := agree258 _ _ (change_representative support p 218 (some 192) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 (some 192))
  rw [sub944]
  exact certified
theorem check615 (p : Pattern) : (!pushGuard support p 244 218 192 192 || decide (bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.boulder 218 + bonus 218 (change p 218 (some 192)))) = true :=
  check_of_implication _ _ (bound615 p)
theorem guard616 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 270 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound616 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 270 .south = true) : bonus 244 p ≤ bonus 270 p := by
  have certified := compare897 p (guard616 p guard)
  simpa only [at244, at270, Int.zero_add] using certified
theorem check616 (p : Pattern) : (!walkGuard soko1_2.board support p 244 270 .south || decide (bonus 244 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound616 p)
theorem guard617 (p : Pattern) (guard : pushGuard support p 244 270 296 296 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound617 (p : Pattern) (guard : pushGuard support p 244 270 296 296 = true) : bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder 296 - Generated.soko1_2Potential.boulder 270 + bonus 270 (change p 270 (some 296)) := by
  have certified := compare5431 p (guard617 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 270 (some 296))
  have normalized := agree258 _ _ (change_representative support p 270 (some 296) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check617 (p : Pattern) : (!pushGuard support p 244 270 296 296 || decide (bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder 296 - Generated.soko1_2Potential.boulder 270 + bonus 270 (change p 270 (some 296)))) = true :=
  check_of_implication _ _ (bound617 p)
theorem guard618 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 245 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound618 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 245 .east = true) : bonus 244 p ≤ bonus 245 p := by
  have certified := compare897 p (guard618 p guard)
  simpa only [at244, at245, Int.zero_add] using certified
theorem check618 (p : Pattern) : (!walkGuard soko1_2.board support p 244 245 .east || decide (bonus 244 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound618 p)
theorem guard619 (p : Pattern) (guard : pushGuard support p 244 245 246 246 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound619 (p : Pattern) (guard : pushGuard support p 244 245 246 246 = true) : bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder 246 - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some 246)) := by
  have certified := compare5431 p (guard619 p guard)
  change d258 p ≤ (1 : Int) + d258 (change p 245 (some 246))
  have normalized := agree258 _ _ (change_representative support p 245 (some 246) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (1 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check619 (p : Pattern) : (!pushGuard support p 244 245 246 246 || decide (bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder 246 - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some 246)))) = true :=
  check_of_implication _ _ (bound619 p)
theorem guard620 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 219 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound620 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 219 .northEast = true) : bonus 244 p ≤ bonus 219 p := by
  have certified := compare897 p (guard620 p guard)
  simpa only [at244, at219, Int.zero_add] using certified
theorem check620 (p : Pattern) : (!walkGuard soko1_2.board support p 244 219 .northEast || decide (bonus 244 p ≤ bonus 219 p)) = true :=
  check_of_implication _ _ (bound620 p)
theorem guard621 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 271 .southEast = true) : d1233 p = 1 := by
  change (!false && !(p 271) && !(true && false && false)) = true at guard
  cases h271 : p 271
  all_goals simp [d0, d1, d1233, h271] at guard ⊢
theorem bound621 (p : Pattern) (guard : walkGuard soko1_2.board support p 244 271 .southEast = true) : bonus 244 p ≤ bonus 271 p := by
  have certified := compare6080 p (guard621 p guard)
  simpa only [at244, at271, Int.zero_add] using certified
theorem check621 (p : Pattern) : (!walkGuard soko1_2.board support p 244 271 .southEast || decide (bonus 244 p ≤ bonus 271 p)) = true :=
  check_of_implication _ _ (bound621 p)
theorem guard622 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 219 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound622 (p : Pattern) (guard : walkGuard soko1_2.board support p 245 219 .north = true) : bonus 245 p ≤ bonus 219 p := by
  have certified := compare897 p (guard622 p guard)
  simpa only [at245, at219, Int.zero_add] using certified
theorem check622 (p : Pattern) : (!walkGuard soko1_2.board support p 245 219 .north || decide (bonus 245 p ≤ bonus 219 p)) = true :=
  check_of_implication _ _ (bound622 p)
theorem guard623 (p : Pattern) (guard : pushGuard support p 245 219 193 193 = true) : d917 p = 1 := by
  change (!false && (!false || false) && !(p 193) && (!(p 193) || false)) = true at guard
  cases h193 : p 193
  all_goals simp [d0, d1, d917, h193] at guard ⊢
theorem bound623 (p : Pattern) (guard : pushGuard support p 245 219 193 193 = true) : bonus 245 p ≤ 1 + Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some 193)) := by
  have certified := compare6131 p (guard623 p guard)
  change d258 p ≤ (0 : Int) + d258 (change p 219 (some 193))
  have normalized := agree258 _ _ (change_representative support p 219 (some 193) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d258 (change p 10000 (some 193))
  rw [sub1022]
  exact certified
theorem check623 (p : Pattern) : (!pushGuard support p 245 219 193 193 || decide (bonus 245 p ≤ 1 + Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some 193)))) = true :=
  check_of_implication _ _ (bound623 p)
end NetHack.Sokoban12CostPartition
