import NetHack.Sokoban32Refined.ActionBounds044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard1080 (p : Pattern) (guard : pushGuard support p 241 267 293 293 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1080 (p : Pattern) (guard : pushGuard support p 241 267 293 293 = true) : bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder 293 - Generated.soko3_2Potential.boulder 267 + bonus 267 (change p 267 (some 293)) := by
  have certified := compare0 p (guard1080 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 267 (some 293))
  have normalized := agree134 _ _ (change_representative support p 267 (some 293) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1080 (p : Pattern) : (!pushGuard support p 241 267 293 293 || decide (bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder 293 - Generated.soko3_2Potential.boulder 267 + bonus 267 (change p 267 (some 293)))) = true :=
  check_of_implication _ _ (bound1080 p)
theorem guard1081 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 242 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1081 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 242 .east = true) : bonus 241 p ≤ bonus 242 p := by
  have certified := compare0 p (guard1081 p guard)
  simpa only [at241, at242, Int.zero_add] using certified
theorem check1081 (p : Pattern) : (!walkGuard soko3_2.board support p 241 242 .east || decide (bonus 241 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound1081 p)
theorem guard1082 (p : Pattern) (guard : pushGuard support p 241 242 243 243 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1082 (p : Pattern) (guard : pushGuard support p 241 242 243 243 = true) : bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder 243 - Generated.soko3_2Potential.boulder 242 + bonus 242 (change p 242 (some 243)) := by
  have certified := compare0 p (guard1082 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 242 (some 243))
  have normalized := agree134 _ _ (change_representative support p 242 (some 243) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1082 (p : Pattern) : (!pushGuard support p 241 242 243 243 || decide (bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder 243 - Generated.soko3_2Potential.boulder 242 + bonus 242 (change p 242 (some 243)))) = true :=
  check_of_implication _ _ (bound1082 p)
theorem guard1083 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 216 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1083 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 216 .northEast = true) : bonus 241 p ≤ bonus 216 p := by
  have certified := compare0 p (guard1083 p guard)
  simpa only [at241, at216, Int.zero_add] using certified
theorem check1083 (p : Pattern) : (!walkGuard soko3_2.board support p 241 216 .northEast || decide (bonus 241 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound1083 p)
theorem guard1084 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 214 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1084 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 214 .northWest = true) : bonus 241 p ≤ bonus 214 p := by
  have certified := compare0 p (guard1084 p guard)
  simpa only [at241, at214, Int.zero_add] using certified
theorem check1084 (p : Pattern) : (!walkGuard soko3_2.board support p 241 214 .northWest || decide (bonus 241 p ≤ bonus 214 p)) = true :=
  check_of_implication _ _ (bound1084 p)
theorem guard1085 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 266 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1085 (p : Pattern) (guard : walkGuard soko3_2.board support p 241 266 .southWest = true) : bonus 241 p ≤ bonus 266 p := by
  have certified := compare0 p (guard1085 p guard)
  simpa only [at241, at266, Int.zero_add] using certified
theorem check1085 (p : Pattern) : (!walkGuard soko3_2.board support p 241 266 .southWest || decide (bonus 241 p ≤ bonus 266 p)) = true :=
  check_of_implication _ _ (bound1085 p)
theorem guard1086 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 216 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1086 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 216 .north = true) : bonus 242 p ≤ bonus 216 p := by
  have certified := compare0 p (guard1086 p guard)
  simpa only [at242, at216, Int.zero_add] using certified
theorem check1086 (p : Pattern) : (!walkGuard soko3_2.board support p 242 216 .north || decide (bonus 242 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound1086 p)
theorem guard1087 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 243 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1087 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 243 .east = true) : bonus 242 p ≤ bonus 243 p := by
  have certified := compare0 p (guard1087 p guard)
  simpa only [at242, at243, Int.zero_add] using certified
theorem check1087 (p : Pattern) : (!walkGuard soko3_2.board support p 242 243 .east || decide (bonus 242 p ≤ bonus 243 p)) = true :=
  check_of_implication _ _ (bound1087 p)
theorem guard1088 (p : Pattern) (guard : pushGuard support p 242 243 244 244 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1088 (p : Pattern) (guard : pushGuard support p 242 243 244 244 = true) : bonus 242 p ≤ 1 + Generated.soko3_2Potential.boulder 244 - Generated.soko3_2Potential.boulder 243 + bonus 243 (change p 243 (some 244)) := by
  have certified := compare0 p (guard1088 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 243 (some 244))
  have normalized := agree134 _ _ (change_representative support p 243 (some 244) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1088 (p : Pattern) : (!pushGuard support p 242 243 244 244 || decide (bonus 242 p ≤ 1 + Generated.soko3_2Potential.boulder 244 - Generated.soko3_2Potential.boulder 243 + bonus 243 (change p 243 (some 244)))) = true :=
  check_of_implication _ _ (bound1088 p)
theorem guard1089 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 241 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1089 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 241 .west = true) : bonus 242 p ≤ bonus 241 p := by
  have certified := compare0 p (guard1089 p guard)
  simpa only [at242, at241, Int.zero_add] using certified
theorem check1089 (p : Pattern) : (!walkGuard soko3_2.board support p 242 241 .west || decide (bonus 242 p ≤ bonus 241 p)) = true :=
  check_of_implication _ _ (bound1089 p)
theorem guard1090 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 215 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1090 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 215 .northWest = true) : bonus 242 p ≤ bonus 215 p := by
  have certified := compare0 p (guard1090 p guard)
  simpa only [at242, at215, Int.zero_add] using certified
theorem check1090 (p : Pattern) : (!walkGuard soko3_2.board support p 242 215 .northWest || decide (bonus 242 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound1090 p)
theorem guard1091 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 269 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1091 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 269 .southEast = true) : bonus 242 p ≤ bonus 269 p := by
  have certified := compare0 p (guard1091 p guard)
  simpa only [at242, at269, Int.zero_add] using certified
theorem check1091 (p : Pattern) : (!walkGuard soko3_2.board support p 242 269 .southEast || decide (bonus 242 p ≤ bonus 269 p)) = true :=
  check_of_implication _ _ (bound1091 p)
theorem guard1092 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 267 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1092 (p : Pattern) (guard : walkGuard soko3_2.board support p 242 267 .southWest = true) : bonus 242 p ≤ bonus 267 p := by
  have certified := compare0 p (guard1092 p guard)
  simpa only [at242, at267, Int.zero_add] using certified
theorem check1092 (p : Pattern) : (!walkGuard soko3_2.board support p 242 267 .southWest || decide (bonus 242 p ≤ bonus 267 p)) = true :=
  check_of_implication _ _ (bound1092 p)
theorem guard1093 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 269 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1093 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 269 .south = true) : bonus 243 p ≤ bonus 269 p := by
  have certified := compare0 p (guard1093 p guard)
  simpa only [at243, at269, Int.zero_add] using certified
theorem check1093 (p : Pattern) : (!walkGuard soko3_2.board support p 243 269 .south || decide (bonus 243 p ≤ bonus 269 p)) = true :=
  check_of_implication _ _ (bound1093 p)
theorem guard1094 (p : Pattern) (guard : pushGuard support p 243 269 295 295 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1094 (p : Pattern) (guard : pushGuard support p 243 269 295 295 = true) : bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder 295 - Generated.soko3_2Potential.boulder 269 + bonus 269 (change p 269 (some 295)) := by
  have certified := compare4301 p (guard1094 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 269 (some 295))
  have normalized := agree134 _ _ (change_representative support p 269 (some 295) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1094 (p : Pattern) : (!pushGuard support p 243 269 295 295 || decide (bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder 295 - Generated.soko3_2Potential.boulder 269 + bonus 269 (change p 269 (some 295)))) = true :=
  check_of_implication _ _ (bound1094 p)
theorem guard1095 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 244 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1095 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 244 .east = true) : bonus 243 p ≤ bonus 244 p := by
  have certified := compare0 p (guard1095 p guard)
  simpa only [at243, at244, Int.zero_add] using certified
theorem check1095 (p : Pattern) : (!walkGuard soko3_2.board support p 243 244 .east || decide (bonus 243 p ≤ bonus 244 p)) = true :=
  check_of_implication _ _ (bound1095 p)
theorem guard1096 (p : Pattern) (guard : pushGuard support p 243 244 245 245 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1096 (p : Pattern) (guard : pushGuard support p 243 244 245 245 = true) : bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder 245 - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some 245)) := by
  have certified := compare9363 p (guard1096 p guard)
  change d134 p ≤ (17 : Int) + d134 (change p 244 (some 245))
  have normalized := agree134 _ _ (change_representative support p 244 (some 245) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (17 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1096 (p : Pattern) : (!pushGuard support p 243 244 245 245 || decide (bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder 245 - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some 245)))) = true :=
  check_of_implication _ _ (bound1096 p)
theorem guard1097 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 242 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1097 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 242 .west = true) : bonus 243 p ≤ bonus 242 p := by
  have certified := compare0 p (guard1097 p guard)
  simpa only [at243, at242, Int.zero_add] using certified
theorem check1097 (p : Pattern) : (!walkGuard soko3_2.board support p 243 242 .west || decide (bonus 243 p ≤ bonus 242 p)) = true :=
  check_of_implication _ _ (bound1097 p)
theorem guard1098 (p : Pattern) (guard : pushGuard support p 243 242 241 241 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1098 (p : Pattern) (guard : pushGuard support p 243 242 241 241 = true) : bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder 241 - Generated.soko3_2Potential.boulder 242 + bonus 242 (change p 242 (some 241)) := by
  have certified := compare9364 p (guard1098 p guard)
  change d134 p ≤ (6 : Int) + d134 (change p 242 (some 241))
  have normalized := agree134 _ _ (change_representative support p 242 (some 241) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (6 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1098 (p : Pattern) : (!pushGuard support p 243 242 241 241 || decide (bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder 241 - Generated.soko3_2Potential.boulder 242 + bonus 242 (change p 242 (some 241)))) = true :=
  check_of_implication _ _ (bound1098 p)
theorem guard1099 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 218 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1099 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 218 .northEast = true) : bonus 243 p ≤ bonus 218 p := by
  have certified := compare0 p (guard1099 p guard)
  simpa only [at243, at218, Int.zero_add] using certified
theorem check1099 (p : Pattern) : (!walkGuard soko3_2.board support p 243 218 .northEast || decide (bonus 243 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound1099 p)
theorem guard1100 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 216 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1100 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 216 .northWest = true) : bonus 243 p ≤ bonus 216 p := by
  have certified := compare0 p (guard1100 p guard)
  simpa only [at243, at216, Int.zero_add] using certified
theorem check1100 (p : Pattern) : (!walkGuard soko3_2.board support p 243 216 .northWest || decide (bonus 243 p ≤ bonus 216 p)) = true :=
  check_of_implication _ _ (bound1100 p)
theorem guard1101 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 270 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1101 (p : Pattern) (guard : walkGuard soko3_2.board support p 243 270 .southEast = true) : bonus 243 p ≤ bonus 270 p := by
  have certified := compare0 p (guard1101 p guard)
  simpa only [at243, at270, Int.zero_add] using certified
theorem check1101 (p : Pattern) : (!walkGuard soko3_2.board support p 243 270 .southEast || decide (bonus 243 p ≤ bonus 270 p)) = true :=
  check_of_implication _ _ (bound1101 p)
theorem guard1102 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 218 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1102 (p : Pattern) (guard : walkGuard soko3_2.board support p 244 218 .north = true) : bonus 244 p ≤ bonus 218 p := by
  have certified := compare0 p (guard1102 p guard)
  simpa only [at244, at218, Int.zero_add] using certified
theorem check1102 (p : Pattern) : (!walkGuard soko3_2.board support p 244 218 .north || decide (bonus 244 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound1102 p)
theorem guard1103 (p : Pattern) (guard : pushGuard support p 244 218 192 192 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound1103 (p : Pattern) (guard : pushGuard support p 244 218 192 192 = true) : bonus 244 p ≤ 1 + Generated.soko3_2Potential.boulder 192 - Generated.soko3_2Potential.boulder 218 + bonus 218 (change p 218 (some 192)) := by
  have certified := compare4301 p (guard1103 p guard)
  change d134 p ≤ (2 : Int) + d134 (change p 218 (some 192))
  have normalized := agree134 _ _ (change_representative support p 218 (some 192) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (2 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check1103 (p : Pattern) : (!pushGuard support p 244 218 192 192 || decide (bonus 244 p ≤ 1 + Generated.soko3_2Potential.boulder 192 - Generated.soko3_2Potential.boulder 218 + bonus 218 (change p 218 (some 192)))) = true :=
  check_of_implication _ _ (bound1103 p)
end NetHack.Sokoban32Refined
