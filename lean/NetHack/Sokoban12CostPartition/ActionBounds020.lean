import NetHack.Sokoban12CostPartition.ActionBounds019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard480 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 237 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound480 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 237 .south = true) : bonus 211 p ≤ bonus 237 p := by
  have certified := compare897 p (guard480 p guard)
  simpa only [at211, at237, Int.zero_add] using certified
theorem check480 (p : Pattern) : (!walkGuard soko1_2.board support p 211 237 .south || decide (bonus 211 p ≤ bonus 237 p)) = true :=
  check_of_implication _ _ (bound480 p)
theorem guard481 (p : Pattern) (guard : pushGuard support p 211 237 263 263 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound481 (p : Pattern) (guard : pushGuard support p 211 237 263 263 = true) : bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder 263 - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some 263)) := by
  have certified := compare2570 p (guard481 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 237 (some 263))
  have normalized := agree258 _ _ (change_representative support p 237 (some 263) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check481 (p : Pattern) : (!pushGuard support p 211 237 263 263 || decide (bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder 263 - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some 263)))) = true :=
  check_of_implication _ _ (bound481 p)
theorem guard482 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 212 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound482 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 212 .east = true) : bonus 211 p ≤ bonus 212 p := by
  have certified := compare897 p (guard482 p guard)
  simpa only [at211, at212, Int.zero_add] using certified
theorem check482 (p : Pattern) : (!walkGuard soko1_2.board support p 211 212 .east || decide (bonus 211 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound482 p)
theorem guard483 (p : Pattern) (guard : pushGuard support p 211 212 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound483 (p : Pattern) (guard : pushGuard support p 211 212 213 213 = true) : bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some 213)) := by
  have certified := compare2570 p (guard483 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 212 (some 213))
  have normalized := agree258 _ _ (change_representative support p 212 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check483 (p : Pattern) : (!pushGuard support p 211 212 213 213 || decide (bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some 213)))) = true :=
  check_of_implication _ _ (bound483 p)
theorem guard484 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 210 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound484 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 210 .west = true) : bonus 211 p ≤ bonus 210 p := by
  have certified := compare897 p (guard484 p guard)
  simpa only [at211, at210, Int.zero_add] using certified
theorem check484 (p : Pattern) : (!walkGuard soko1_2.board support p 211 210 .west || decide (bonus 211 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound484 p)
theorem guard485 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 186 .northEast = true) : d829 p = 1 := by
  change (!false && !(p 186) && !(true && false && false)) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound485 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 186 .northEast = true) : bonus 211 p ≤ bonus 186 p := by
  have certified := compare3692 p (guard485 p guard)
  simpa only [at211, at186, Int.zero_add] using certified
theorem check485 (p : Pattern) : (!walkGuard soko1_2.board support p 211 186 .northEast || decide (bonus 211 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound485 p)
theorem guard486 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 184 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound486 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 184 .northWest = true) : bonus 211 p ≤ bonus 184 p := by
  have certified := compare897 p (guard486 p guard)
  simpa only [at211, at184, Int.zero_add] using certified
theorem check486 (p : Pattern) : (!walkGuard soko1_2.board support p 211 184 .northWest || decide (bonus 211 p ≤ bonus 184 p)) = true :=
  check_of_implication _ _ (bound486 p)
theorem guard487 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 238 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound487 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 238 .southEast = true) : bonus 211 p ≤ bonus 238 p := by
  have certified := compare897 p (guard487 p guard)
  simpa only [at211, at238, Int.zero_add] using certified
theorem check487 (p : Pattern) : (!walkGuard soko1_2.board support p 211 238 .southEast || decide (bonus 211 p ≤ bonus 238 p)) = true :=
  check_of_implication _ _ (bound487 p)
theorem guard488 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 236 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound488 (p : Pattern) (guard : walkGuard soko1_2.board support p 211 236 .southWest = true) : bonus 211 p ≤ bonus 236 p := by
  have certified := compare897 p (guard488 p guard)
  simpa only [at211, at236, Int.zero_add] using certified
theorem check488 (p : Pattern) : (!walkGuard soko1_2.board support p 211 236 .southWest || decide (bonus 211 p ≤ bonus 236 p)) = true :=
  check_of_implication _ _ (bound488 p)
theorem guard489 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 186 .north = true) : d829 p = 1 := by
  change (!false && !(p 186) && !false) = true at guard
  cases h186 : p 186
  all_goals simp [d0, d1, d829, h186] at guard ⊢
theorem bound489 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 186 .north = true) : bonus 212 p ≤ bonus 186 p := by
  have certified := compare3692 p (guard489 p guard)
  simpa only [at212, at186, Int.zero_add] using certified
theorem check489 (p : Pattern) : (!walkGuard soko1_2.board support p 212 186 .north || decide (bonus 212 p ≤ bonus 186 p)) = true :=
  check_of_implication _ _ (bound489 p)
theorem guard490 (p : Pattern) (guard : pushGuard support p 212 186 160 160 = true) : d1017 p = 1 := by
  change (!false && (!true || (p 186)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h160 : p 160 <;> cases h186 : p 186
  all_goals simp [d0, d1, d828, d1017, h160, h186] at guard ⊢
theorem bound490 (p : Pattern) (guard : pushGuard support p 212 186 160 160 = true) : bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some 160)) := by
  have certified := compare5687 p (guard490 p guard)
  change d258 p ≤ (0 : Int) + d485 (change p 186 (some 160))
  have normalized := agree485 _ _ (change_representative support p 186 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (0 : Int) + d485 (change p 186 (some 160))
  rw [sub2486]
  exact certified
theorem check490 (p : Pattern) : (!pushGuard support p 212 186 160 160 || decide (bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some 160)))) = true :=
  check_of_implication _ _ (bound490 p)
theorem guard491 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 238 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound491 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 238 .south = true) : bonus 212 p ≤ bonus 238 p := by
  have certified := compare897 p (guard491 p guard)
  simpa only [at212, at238, Int.zero_add] using certified
theorem check491 (p : Pattern) : (!walkGuard soko1_2.board support p 212 238 .south || decide (bonus 212 p ≤ bonus 238 p)) = true :=
  check_of_implication _ _ (bound491 p)
theorem guard492 (p : Pattern) (guard : pushGuard support p 212 238 264 264 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound492 (p : Pattern) (guard : pushGuard support p 212 238 264 264 = true) : bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder 264 - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some 264)) := by
  have certified := compare2570 p (guard492 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 238 (some 264))
  have normalized := agree258 _ _ (change_representative support p 238 (some 264) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check492 (p : Pattern) : (!pushGuard support p 212 238 264 264 || decide (bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder 264 - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some 264)))) = true :=
  check_of_implication _ _ (bound492 p)
theorem guard493 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 213 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound493 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 213 .east = true) : bonus 212 p ≤ bonus 213 p := by
  have certified := compare897 p (guard493 p guard)
  simpa only [at212, at213, Int.zero_add] using certified
theorem check493 (p : Pattern) : (!walkGuard soko1_2.board support p 212 213 .east || decide (bonus 212 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound493 p)
theorem guard494 (p : Pattern) (guard : pushGuard support p 212 213 214 214 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound494 (p : Pattern) (guard : pushGuard support p 212 213 214 214 = true) : bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder 214 - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some 214)) := by
  have certified := compare2570 p (guard494 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 213 (some 214))
  have normalized := agree258 _ _ (change_representative support p 213 (some 214) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check494 (p : Pattern) : (!pushGuard support p 212 213 214 214 || decide (bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder 214 - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some 214)))) = true :=
  check_of_implication _ _ (bound494 p)
theorem guard495 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 211 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound495 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 211 .west = true) : bonus 212 p ≤ bonus 211 p := by
  have certified := compare897 p (guard495 p guard)
  simpa only [at212, at211, Int.zero_add] using certified
theorem check495 (p : Pattern) : (!walkGuard soko1_2.board support p 212 211 .west || decide (bonus 212 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound495 p)
theorem guard496 (p : Pattern) (guard : pushGuard support p 212 211 210 210 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound496 (p : Pattern) (guard : pushGuard support p 212 211 210 210 = true) : bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder 210 - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some 210)) := by
  have certified := compare2570 p (guard496 p guard)
  change d258 p ≤ (2 : Int) + d258 (change p 211 (some 210))
  have normalized := agree258 _ _ (change_representative support p 211 (some 210) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d258 (change p 10000 none)
  rw [sub1222]
  exact certified
theorem check496 (p : Pattern) : (!pushGuard support p 212 211 210 210 || decide (bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder 210 - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some 210)))) = true :=
  check_of_implication _ _ (bound496 p)
theorem guard497 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 187 .northEast = true) : d851 p = 1 := by
  change (!false && !(p 187) && !(true && (p 186) && false)) = true at guard
  cases h186 : p 186 <;> cases h187 : p 187
  all_goals simp [d0, d1, d851, h186, h187] at guard ⊢
theorem bound497 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 187 .northEast = true) : bonus 212 p ≤ bonus 187 p := by
  have certified := compare5729 p (guard497 p guard)
  simpa only [at212, at187, Int.zero_add] using certified
theorem check497 (p : Pattern) : (!walkGuard soko1_2.board support p 212 187 .northEast || decide (bonus 212 p ≤ bonus 187 p)) = true :=
  check_of_implication _ _ (bound497 p)
theorem guard498 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 185 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && (p 186) && false)) = true at guard
  cases h186 : p 186
  all_goals simp [d1, h186] at guard ⊢
theorem bound498 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 185 .northWest = true) : bonus 212 p ≤ bonus 185 p := by
  have certified := compare897 p (guard498 p guard)
  simpa only [at212, at185, Int.zero_add] using certified
theorem check498 (p : Pattern) : (!walkGuard soko1_2.board support p 212 185 .northWest || decide (bonus 212 p ≤ bonus 185 p)) = true :=
  check_of_implication _ _ (bound498 p)
theorem guard499 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 239 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound499 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 239 .southEast = true) : bonus 212 p ≤ bonus 239 p := by
  have certified := compare897 p (guard499 p guard)
  simpa only [at212, at239, Int.zero_add] using certified
theorem check499 (p : Pattern) : (!walkGuard soko1_2.board support p 212 239 .southEast || decide (bonus 212 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound499 p)
theorem guard500 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 237 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound500 (p : Pattern) (guard : walkGuard soko1_2.board support p 212 237 .southWest = true) : bonus 212 p ≤ bonus 237 p := by
  have certified := compare897 p (guard500 p guard)
  simpa only [at212, at237, Int.zero_add] using certified
theorem check500 (p : Pattern) : (!walkGuard soko1_2.board support p 212 237 .southWest || decide (bonus 212 p ≤ bonus 237 p)) = true :=
  check_of_implication _ _ (bound500 p)
theorem guard501 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 187 .north = true) : d851 p = 1 := by
  change (!false && !(p 187) && !false) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d851, h187] at guard ⊢
theorem bound501 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 187 .north = true) : bonus 213 p ≤ bonus 187 p := by
  have certified := compare5729 p (guard501 p guard)
  simpa only [at213, at187, Int.zero_add] using certified
theorem check501 (p : Pattern) : (!walkGuard soko1_2.board support p 213 187 .north || decide (bonus 213 p ≤ bonus 187 p)) = true :=
  check_of_implication _ _ (bound501 p)
theorem guard502 (p : Pattern) (guard : pushGuard support p 213 187 161 161 = true) : d850 p = 1 := by
  change (!false && (!true || (p 187)) && !false && (!false || false)) = true at guard
  cases h187 : p 187
  all_goals simp [d0, d1, d850, h187] at guard ⊢
theorem bound502 (p : Pattern) (guard : pushGuard support p 213 187 161 161 = true) : bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder 161 - Generated.soko1_2Potential.boulder 187 + bonus 187 (change p 187 (some 161)) := by
  have certified := compare5789 p (guard502 p guard)
  change d258 p ≤ (2 : Int) + d524 (change p 187 (some 161))
  have normalized := agree524 _ _ (change_representative support p 187 (some 161) 10000 dummy_outside)
  rw [normalized]
  change d258 p ≤ (2 : Int) + d524 (change p 187 none)
  rw [sub1517]
  exact certified
theorem check502 (p : Pattern) : (!pushGuard support p 213 187 161 161 || decide (bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder 161 - Generated.soko1_2Potential.boulder 187 + bonus 187 (change p 187 (some 161)))) = true :=
  check_of_implication _ _ (bound502 p)
theorem guard503 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 239 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound503 (p : Pattern) (guard : walkGuard soko1_2.board support p 213 239 .south = true) : bonus 213 p ≤ bonus 239 p := by
  have certified := compare897 p (guard503 p guard)
  simpa only [at213, at239, Int.zero_add] using certified
theorem check503 (p : Pattern) : (!walkGuard soko1_2.board support p 213 239 .south || decide (bonus 213 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound503 p)
end NetHack.Sokoban12CostPartition
