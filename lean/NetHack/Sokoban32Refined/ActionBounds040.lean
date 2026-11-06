import NetHack.Sokoban32Refined.ActionBounds039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard960 (p : Pattern) (guard : pushGuard support p 212 213 214 214 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound960 (p : Pattern) (guard : pushGuard support p 212 213 214 214 = true) : bonus 212 p ≤ 1 + Generated.soko3_2Potential.boulder 214 - Generated.soko3_2Potential.boulder 213 + bonus 213 (change p 213 (some 214)) := by
  have certified := compare0 p (guard960 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 213 (some 214))
  have normalized := agree134 _ _ (change_representative support p 213 (some 214) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check960 (p : Pattern) : (!pushGuard support p 212 213 214 214 || decide (bonus 212 p ≤ 1 + Generated.soko3_2Potential.boulder 214 - Generated.soko3_2Potential.boulder 213 + bonus 213 (change p 213 (some 214)))) = true :=
  check_of_implication _ _ (bound960 p)
theorem guard961 (p : Pattern) (guard : walkGuard soko3_2.board support p 212 211 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound961 (p : Pattern) (guard : walkGuard soko3_2.board support p 212 211 .west = true) : bonus 212 p ≤ bonus 211 p := by
  have certified := compare0 p (guard961 p guard)
  simpa only [at212, at211, Int.zero_add] using certified
theorem check961 (p : Pattern) : (!walkGuard soko3_2.board support p 212 211 .west || decide (bonus 212 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound961 p)
theorem guard962 (p : Pattern) (guard : pushGuard support p 212 211 210 210 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound962 (p : Pattern) (guard : pushGuard support p 212 211 210 210 = true) : bonus 212 p ≤ 1 + Generated.soko3_2Potential.boulder 210 - Generated.soko3_2Potential.boulder 211 + bonus 211 (change p 211 (some 210)) := by
  have certified := compare4301 p (guard962 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 211 (some 210))
  have normalized := agree134 _ _ (change_representative support p 211 (some 210) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check962 (p : Pattern) : (!pushGuard support p 212 211 210 210 || decide (bonus 212 p ≤ 1 + Generated.soko3_2Potential.boulder 210 - Generated.soko3_2Potential.boulder 211 + bonus 211 (change p 211 (some 210)))) = true :=
  check_of_implication _ _ (bound962 p)
theorem guard963 (p : Pattern) (guard : walkGuard soko3_2.board support p 212 239 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound963 (p : Pattern) (guard : walkGuard soko3_2.board support p 212 239 .southEast = true) : bonus 212 p ≤ bonus 239 p := by
  have certified := compare0 p (guard963 p guard)
  simpa only [at212, at239, Int.zero_add] using certified
theorem check963 (p : Pattern) : (!walkGuard soko3_2.board support p 212 239 .southEast || decide (bonus 212 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound963 p)
theorem guard964 (p : Pattern) (guard : walkGuard soko3_2.board support p 213 239 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound964 (p : Pattern) (guard : walkGuard soko3_2.board support p 213 239 .south = true) : bonus 213 p ≤ bonus 239 p := by
  have certified := compare0 p (guard964 p guard)
  simpa only [at213, at239, Int.zero_add] using certified
theorem check964 (p : Pattern) : (!walkGuard soko3_2.board support p 213 239 .south || decide (bonus 213 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound964 p)
theorem guard965 (p : Pattern) (guard : pushGuard support p 213 239 265 265 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound965 (p : Pattern) (guard : pushGuard support p 213 239 265 265 = true) : bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder 265 - Generated.soko3_2Potential.boulder 239 + bonus 239 (change p 239 (some 265)) := by
  have certified := compare0 p (guard965 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 239 (some 265))
  have normalized := agree134 _ _ (change_representative support p 239 (some 265) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check965 (p : Pattern) : (!pushGuard support p 213 239 265 265 || decide (bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder 265 - Generated.soko3_2Potential.boulder 239 + bonus 239 (change p 239 (some 265)))) = true :=
  check_of_implication _ _ (bound965 p)
theorem guard966 (p : Pattern) (guard : walkGuard soko3_2.board support p 213 214 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound966 (p : Pattern) (guard : walkGuard soko3_2.board support p 213 214 .east = true) : bonus 213 p ≤ bonus 214 p := by
  have certified := compare0 p (guard966 p guard)
  simpa only [at213, at214, Int.zero_add] using certified
theorem check966 (p : Pattern) : (!walkGuard soko3_2.board support p 213 214 .east || decide (bonus 213 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound966 p)
theorem guard967 (p : Pattern) (guard : pushGuard support p 213 214 215 215 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound967 (p : Pattern) (guard : pushGuard support p 213 214 215 215 = true) : bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.boulder 214 + bonus 214 (change p 214 (some 215)) := by
  have certified := compare0 p (guard967 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 214 (some 215))
  have normalized := agree134 _ _ (change_representative support p 214 (some 215) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check967 (p : Pattern) : (!pushGuard support p 213 214 215 215 || decide (bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.boulder 214 + bonus 214 (change p 214 (some 215)))) = true :=
  check_of_implication _ _ (bound967 p)
theorem guard968 (p : Pattern) (guard : walkGuard soko3_2.board support p 213 212 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound968 (p : Pattern) (guard : walkGuard soko3_2.board support p 213 212 .west = true) : bonus 213 p ≤ bonus 212 p := by
  have certified := compare0 p (guard968 p guard)
  simpa only [at213, at212, Int.zero_add] using certified
theorem check968 (p : Pattern) : (!walkGuard soko3_2.board support p 213 212 .west || decide (bonus 213 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound968 p)
theorem guard969 (p : Pattern) (guard : pushGuard support p 213 212 211 211 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound969 (p : Pattern) (guard : pushGuard support p 213 212 211 211 = true) : bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder 211 - Generated.soko3_2Potential.boulder 212 + bonus 212 (change p 212 (some 211)) := by
  have certified := compare4301 p (guard969 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 212 (some 211))
  have normalized := agree134 _ _ (change_representative support p 212 (some 211) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check969 (p : Pattern) : (!pushGuard support p 213 212 211 211 || decide (bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder 211 - Generated.soko3_2Potential.boulder 212 + bonus 212 (change p 212 (some 211)))) = true :=
  check_of_implication _ _ (bound969 p)
theorem guard970 (p : Pattern) (guard : walkGuard soko3_2.board support p 213 188 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound970 (p : Pattern) (guard : walkGuard soko3_2.board support p 213 188 .northEast = true) : bonus 213 p ≤ bonus 188 p := by
  have certified := compare0 p (guard970 p guard)
  simpa only [at213, at188, Int.zero_add] using certified
theorem check970 (p : Pattern) : (!walkGuard soko3_2.board support p 213 188 .northEast || decide (bonus 213 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound970 p)
theorem guard971 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 188 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound971 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 188 .north = true) : bonus 214 p ≤ bonus 188 p := by
  have certified := compare0 p (guard971 p guard)
  simpa only [at214, at188, Int.zero_add] using certified
theorem check971 (p : Pattern) : (!walkGuard soko3_2.board support p 214 188 .north || decide (bonus 214 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound971 p)
theorem guard972 (p : Pattern) (guard : pushGuard support p 214 188 162 162 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound972 (p : Pattern) (guard : pushGuard support p 214 188 162 162 = true) : bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.boulder 188 + bonus 188 (change p 188 (some 162)) := by
  have certified := compare4301 p (guard972 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 188 (some 162))
  have normalized := agree134 _ _ (change_representative support p 188 (some 162) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check972 (p : Pattern) : (!pushGuard support p 214 188 162 162 || decide (bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.boulder 188 + bonus 188 (change p 188 (some 162)))) = true :=
  check_of_implication _ _ (bound972 p)
theorem guard973 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 215 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound973 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 215 .east = true) : bonus 214 p ≤ bonus 215 p := by
  have certified := compare0 p (guard973 p guard)
  simpa only [at214, at215, Int.zero_add] using certified
theorem check973 (p : Pattern) : (!walkGuard soko3_2.board support p 214 215 .east || decide (bonus 214 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound973 p)
theorem guard974 (p : Pattern) (guard : pushGuard support p 214 215 216 216 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound974 (p : Pattern) (guard : pushGuard support p 214 215 216 216 = true) : bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder 216 - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some 216)) := by
  have certified := compare9361 p (guard974 p guard)
  change d134 p ≤ (9 : Int) + d134 (change p 215 (some 216))
  have normalized := agree134 _ _ (change_representative support p 215 (some 216) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (9 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check974 (p : Pattern) : (!pushGuard support p 214 215 216 216 || decide (bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder 216 - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some 216)))) = true :=
  check_of_implication _ _ (bound974 p)
theorem guard975 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 213 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound975 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 213 .west = true) : bonus 214 p ≤ bonus 213 p := by
  have certified := compare0 p (guard975 p guard)
  simpa only [at214, at213, Int.zero_add] using certified
theorem check975 (p : Pattern) : (!walkGuard soko3_2.board support p 214 213 .west || decide (bonus 214 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound975 p)
theorem guard976 (p : Pattern) (guard : pushGuard support p 214 213 212 212 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound976 (p : Pattern) (guard : pushGuard support p 214 213 212 212 = true) : bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder 212 - Generated.soko3_2Potential.boulder 213 + bonus 213 (change p 213 (some 212)) := by
  have certified := compare4301 p (guard976 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 213 (some 212))
  have normalized := agree134 _ _ (change_representative support p 213 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check976 (p : Pattern) : (!pushGuard support p 214 213 212 212 || decide (bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder 212 - Generated.soko3_2Potential.boulder 213 + bonus 213 (change p 213 (some 212)))) = true :=
  check_of_implication _ _ (bound976 p)
theorem guard977 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 189 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound977 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 189 .northEast = true) : bonus 214 p ≤ bonus 189 p := by
  have certified := compare0 p (guard977 p guard)
  simpa only [at214, at189, Int.zero_add] using certified
theorem check977 (p : Pattern) : (!walkGuard soko3_2.board support p 214 189 .northEast || decide (bonus 214 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound977 p)
theorem guard978 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 241 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound978 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 241 .southEast = true) : bonus 214 p ≤ bonus 241 p := by
  have certified := compare0 p (guard978 p guard)
  simpa only [at214, at241, Int.zero_add] using certified
theorem check978 (p : Pattern) : (!walkGuard soko3_2.board support p 214 241 .southEast || decide (bonus 214 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound978 p)
theorem guard979 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 239 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound979 (p : Pattern) (guard : walkGuard soko3_2.board support p 214 239 .southWest = true) : bonus 214 p ≤ bonus 239 p := by
  have certified := compare0 p (guard979 p guard)
  simpa only [at214, at239, Int.zero_add] using certified
theorem check979 (p : Pattern) : (!walkGuard soko3_2.board support p 214 239 .southWest || decide (bonus 214 p ≤ bonus 239 p)) = true :=
  check_of_implication _ _ (bound979 p)
theorem guard980 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 189 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound980 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 189 .north = true) : bonus 215 p ≤ bonus 189 p := by
  have certified := compare0 p (guard980 p guard)
  simpa only [at215, at189, Int.zero_add] using certified
theorem check980 (p : Pattern) : (!walkGuard soko3_2.board support p 215 189 .north || decide (bonus 215 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound980 p)
theorem guard981 (p : Pattern) (guard : pushGuard support p 215 189 163 163 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound981 (p : Pattern) (guard : pushGuard support p 215 189 163 163 = true) : bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder 163 - Generated.soko3_2Potential.boulder 189 + bonus 189 (change p 189 (some 163)) := by
  have certified := compare4301 p (guard981 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 189 (some 163))
  have normalized := agree134 _ _ (change_representative support p 189 (some 163) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check981 (p : Pattern) : (!pushGuard support p 215 189 163 163 || decide (bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder 163 - Generated.soko3_2Potential.boulder 189 + bonus 189 (change p 189 (some 163)))) = true :=
  check_of_implication _ _ (bound981 p)
theorem guard982 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 241 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound982 (p : Pattern) (guard : walkGuard soko3_2.board support p 215 241 .south = true) : bonus 215 p ≤ bonus 241 p := by
  have certified := compare0 p (guard982 p guard)
  simpa only [at215, at241, Int.zero_add] using certified
theorem check982 (p : Pattern) : (!walkGuard soko3_2.board support p 215 241 .south || decide (bonus 215 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound982 p)
theorem guard983 (p : Pattern) (guard : pushGuard support p 215 241 267 267 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound983 (p : Pattern) (guard : pushGuard support p 215 241 267 267 = true) : bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder 267 - Generated.soko3_2Potential.boulder 241 + bonus 241 (change p 241 (some 267)) := by
  have certified := compare0 p (guard983 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 241 (some 267))
  have normalized := agree134 _ _ (change_representative support p 241 (some 267) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check983 (p : Pattern) : (!pushGuard support p 215 241 267 267 || decide (bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder 267 - Generated.soko3_2Potential.boulder 241 + bonus 241 (change p 241 (some 267)))) = true :=
  check_of_implication _ _ (bound983 p)
end NetHack.Sokoban32Refined
