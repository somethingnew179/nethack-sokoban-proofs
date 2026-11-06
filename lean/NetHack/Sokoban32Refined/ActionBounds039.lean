import NetHack.Sokoban32Refined.ActionBounds038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard936 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 230 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound936 (p : Pattern) (guard : walkGuard soko3_2.board support p 205 230 .southWest = true) : bonus 205 p ≤ bonus 230 p := by
  have certified := compare103 p (guard936 p guard)
  simpa only [at205, at230, Int.zero_add] using certified
theorem check936 (p : Pattern) : (!walkGuard soko3_2.board support p 205 230 .southWest || decide (bonus 205 p ≤ bonus 230 p)) = true :=
  check_of_implication _ _ (bound936 p)
theorem guard937 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 180 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound937 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 180 .north = true) : bonus 206 p ≤ bonus 180 p := by
  have certified := compare103 p (guard937 p guard)
  simpa only [at206, at180, Int.zero_add] using certified
theorem check937 (p : Pattern) : (!walkGuard soko3_2.board support p 206 180 .north || decide (bonus 206 p ≤ bonus 180 p)) = true :=
  check_of_implication _ _ (bound937 p)
theorem guard938 (p : Pattern) (guard : pushGuard support p 206 180 154 154 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound938 (p : Pattern) (guard : pushGuard support p 206 180 154 154 = true) : bonus 206 p ≤ 1 + Generated.soko3_2Potential.boulder 154 - Generated.soko3_2Potential.boulder 180 + bonus 180 (change p 180 (some 154)) := by
  have certified := compare37 p (guard938 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 180 (some 154))
  have normalized := agree0 _ _ (change_representative support p 180 (some 154) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check938 (p : Pattern) : (!pushGuard support p 206 180 154 154 || decide (bonus 206 p ≤ 1 + Generated.soko3_2Potential.boulder 154 - Generated.soko3_2Potential.boulder 180 + bonus 180 (change p 180 (some 154)))) = true :=
  check_of_implication _ _ (bound938 p)
theorem guard939 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 232 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound939 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 232 .south = true) : bonus 206 p ≤ bonus 232 p := by
  have certified := compare103 p (guard939 p guard)
  simpa only [at206, at232, Int.zero_add] using certified
theorem check939 (p : Pattern) : (!walkGuard soko3_2.board support p 206 232 .south || decide (bonus 206 p ≤ bonus 232 p)) = true :=
  check_of_implication _ _ (bound939 p)
theorem guard940 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 205 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound940 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 205 .west = true) : bonus 206 p ≤ bonus 205 p := by
  have certified := compare103 p (guard940 p guard)
  simpa only [at206, at205, Int.zero_add] using certified
theorem check940 (p : Pattern) : (!walkGuard soko3_2.board support p 206 205 .west || decide (bonus 206 p ≤ bonus 205 p)) = true :=
  check_of_implication _ _ (bound940 p)
theorem guard941 (p : Pattern) (guard : pushGuard support p 206 205 204 204 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound941 (p : Pattern) (guard : pushGuard support p 206 205 204 204 = true) : bonus 206 p ≤ 1 + Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some 204)) := by
  have certified := compare37 p (guard941 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 205 (some 204))
  have normalized := agree0 _ _ (change_representative support p 205 (some 204) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check941 (p : Pattern) : (!pushGuard support p 206 205 204 204 || decide (bonus 206 p ≤ 1 + Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some 204)))) = true :=
  check_of_implication _ _ (bound941 p)
theorem guard942 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 179 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound942 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 179 .northWest = true) : bonus 206 p ≤ bonus 179 p := by
  have certified := compare103 p (guard942 p guard)
  simpa only [at206, at179, Int.zero_add] using certified
theorem check942 (p : Pattern) : (!walkGuard soko3_2.board support p 206 179 .northWest || decide (bonus 206 p ≤ bonus 179 p)) = true :=
  check_of_implication _ _ (bound942 p)
theorem guard943 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 231 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound943 (p : Pattern) (guard : walkGuard soko3_2.board support p 206 231 .southWest = true) : bonus 206 p ≤ bonus 231 p := by
  have certified := compare103 p (guard943 p guard)
  simpa only [at206, at231, Int.zero_add] using certified
theorem check943 (p : Pattern) : (!walkGuard soko3_2.board support p 206 231 .southWest || decide (bonus 206 p ≤ bonus 231 p)) = true :=
  check_of_implication _ _ (bound943 p)
theorem guard944 (p : Pattern) (guard : walkGuard soko3_2.board support p 209 183 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound944 (p : Pattern) (guard : walkGuard soko3_2.board support p 209 183 .north = true) : bonus 209 p ≤ bonus 183 p := by
  have certified := compare0 p (guard944 p guard)
  simpa only [at209, at183, Int.zero_add] using certified
theorem check944 (p : Pattern) : (!walkGuard soko3_2.board support p 209 183 .north || decide (bonus 209 p ≤ bonus 183 p)) = true :=
  check_of_implication _ _ (bound944 p)
theorem guard945 (p : Pattern) (guard : pushGuard support p 209 183 157 157 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound945 (p : Pattern) (guard : pushGuard support p 209 183 157 157 = true) : bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder 157 - Generated.soko3_2Potential.boulder 183 + bonus 183 (change p 183 (some 157)) := by
  have certified := compare104 p (guard945 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 183 (some 157))
  have normalized := agree134 _ _ (change_representative support p 183 (some 157) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check945 (p : Pattern) : (!pushGuard support p 209 183 157 157 || decide (bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder 157 - Generated.soko3_2Potential.boulder 183 + bonus 183 (change p 183 (some 157)))) = true :=
  check_of_implication _ _ (bound945 p)
theorem guard946 (p : Pattern) (guard : walkGuard soko3_2.board support p 209 235 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound946 (p : Pattern) (guard : walkGuard soko3_2.board support p 209 235 .south = true) : bonus 209 p ≤ bonus 235 p := by
  have certified := compare0 p (guard946 p guard)
  simpa only [at209, at235, Int.zero_add] using certified
theorem check946 (p : Pattern) : (!walkGuard soko3_2.board support p 209 235 .south || decide (bonus 209 p ≤ bonus 235 p)) = true :=
  check_of_implication _ _ (bound946 p)
theorem guard947 (p : Pattern) (guard : pushGuard support p 209 235 261 261 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound947 (p : Pattern) (guard : pushGuard support p 209 235 261 261 = true) : bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder 261 - Generated.soko3_2Potential.boulder 235 + bonus 235 (change p 235 (some 261)) := by
  have certified := compare104 p (guard947 p guard)
  change d134 p ≤ (1 : Int) + d134 (change p 235 (some 261))
  have normalized := agree134 _ _ (change_representative support p 235 (some 261) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (1 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check947 (p : Pattern) : (!pushGuard support p 209 235 261 261 || decide (bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder 261 - Generated.soko3_2Potential.boulder 235 + bonus 235 (change p 235 (some 261)))) = true :=
  check_of_implication _ _ (bound947 p)
theorem guard948 (p : Pattern) (guard : walkGuard soko3_2.board support p 209 210 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound948 (p : Pattern) (guard : walkGuard soko3_2.board support p 209 210 .east = true) : bonus 209 p ≤ bonus 210 p := by
  have certified := compare0 p (guard948 p guard)
  simpa only [at209, at210, Int.zero_add] using certified
theorem check948 (p : Pattern) : (!walkGuard soko3_2.board support p 209 210 .east || decide (bonus 209 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound948 p)
theorem guard949 (p : Pattern) (guard : pushGuard support p 209 210 211 211 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound949 (p : Pattern) (guard : pushGuard support p 209 210 211 211 = true) : bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder 211 - Generated.soko3_2Potential.boulder 210 + bonus 210 (change p 210 (some 211)) := by
  have certified := compare0 p (guard949 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 210 (some 211))
  have normalized := agree134 _ _ (change_representative support p 210 (some 211) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check949 (p : Pattern) : (!pushGuard support p 209 210 211 211 || decide (bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder 211 - Generated.soko3_2Potential.boulder 210 + bonus 210 (change p 210 (some 211)))) = true :=
  check_of_implication _ _ (bound949 p)
theorem guard950 (p : Pattern) (guard : walkGuard soko3_2.board support p 210 211 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound950 (p : Pattern) (guard : walkGuard soko3_2.board support p 210 211 .east = true) : bonus 210 p ≤ bonus 211 p := by
  have certified := compare0 p (guard950 p guard)
  simpa only [at210, at211, Int.zero_add] using certified
theorem check950 (p : Pattern) : (!walkGuard soko3_2.board support p 210 211 .east || decide (bonus 210 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound950 p)
theorem guard951 (p : Pattern) (guard : pushGuard support p 210 211 212 212 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound951 (p : Pattern) (guard : pushGuard support p 210 211 212 212 = true) : bonus 210 p ≤ 1 + Generated.soko3_2Potential.boulder 212 - Generated.soko3_2Potential.boulder 211 + bonus 211 (change p 211 (some 212)) := by
  have certified := compare0 p (guard951 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 211 (some 212))
  have normalized := agree134 _ _ (change_representative support p 211 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check951 (p : Pattern) : (!pushGuard support p 210 211 212 212 || decide (bonus 210 p ≤ 1 + Generated.soko3_2Potential.boulder 212 - Generated.soko3_2Potential.boulder 211 + bonus 211 (change p 211 (some 212)))) = true :=
  check_of_implication _ _ (bound951 p)
theorem guard952 (p : Pattern) (guard : walkGuard soko3_2.board support p 210 209 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound952 (p : Pattern) (guard : walkGuard soko3_2.board support p 210 209 .west = true) : bonus 210 p ≤ bonus 209 p := by
  have certified := compare0 p (guard952 p guard)
  simpa only [at210, at209, Int.zero_add] using certified
theorem check952 (p : Pattern) : (!walkGuard soko3_2.board support p 210 209 .west || decide (bonus 210 p ≤ bonus 209 p)) = true :=
  check_of_implication _ _ (bound952 p)
theorem guard953 (p : Pattern) (guard : walkGuard soko3_2.board support p 210 183 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound953 (p : Pattern) (guard : walkGuard soko3_2.board support p 210 183 .northWest = true) : bonus 210 p ≤ bonus 183 p := by
  have certified := compare0 p (guard953 p guard)
  simpa only [at210, at183, Int.zero_add] using certified
theorem check953 (p : Pattern) : (!walkGuard soko3_2.board support p 210 183 .northWest || decide (bonus 210 p ≤ bonus 183 p)) = true :=
  check_of_implication _ _ (bound953 p)
theorem guard954 (p : Pattern) (guard : walkGuard soko3_2.board support p 210 235 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && true && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound954 (p : Pattern) (guard : walkGuard soko3_2.board support p 210 235 .southWest = true) : bonus 210 p ≤ bonus 235 p := by
  have certified := compare0 p (guard954 p guard)
  simpa only [at210, at235, Int.zero_add] using certified
theorem check954 (p : Pattern) : (!walkGuard soko3_2.board support p 210 235 .southWest || decide (bonus 210 p ≤ bonus 235 p)) = true :=
  check_of_implication _ _ (bound954 p)
theorem guard955 (p : Pattern) (guard : walkGuard soko3_2.board support p 211 212 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound955 (p : Pattern) (guard : walkGuard soko3_2.board support p 211 212 .east = true) : bonus 211 p ≤ bonus 212 p := by
  have certified := compare0 p (guard955 p guard)
  simpa only [at211, at212, Int.zero_add] using certified
theorem check955 (p : Pattern) : (!walkGuard soko3_2.board support p 211 212 .east || decide (bonus 211 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound955 p)
theorem guard956 (p : Pattern) (guard : pushGuard support p 211 212 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound956 (p : Pattern) (guard : pushGuard support p 211 212 213 213 = true) : bonus 211 p ≤ 1 + Generated.soko3_2Potential.boulder 213 - Generated.soko3_2Potential.boulder 212 + bonus 212 (change p 212 (some 213)) := by
  have certified := compare0 p (guard956 p guard)
  change d134 p ≤ (0 : Int) + d134 (change p 212 (some 213))
  have normalized := agree134 _ _ (change_representative support p 212 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (0 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check956 (p : Pattern) : (!pushGuard support p 211 212 213 213 || decide (bonus 211 p ≤ 1 + Generated.soko3_2Potential.boulder 213 - Generated.soko3_2Potential.boulder 212 + bonus 212 (change p 212 (some 213)))) = true :=
  check_of_implication _ _ (bound956 p)
theorem guard957 (p : Pattern) (guard : walkGuard soko3_2.board support p 211 210 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound957 (p : Pattern) (guard : walkGuard soko3_2.board support p 211 210 .west = true) : bonus 211 p ≤ bonus 210 p := by
  have certified := compare0 p (guard957 p guard)
  simpa only [at211, at210, Int.zero_add] using certified
theorem check957 (p : Pattern) : (!walkGuard soko3_2.board support p 211 210 .west || decide (bonus 211 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound957 p)
theorem guard958 (p : Pattern) (guard : pushGuard support p 211 210 209 209 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound958 (p : Pattern) (guard : pushGuard support p 211 210 209 209 = true) : bonus 211 p ≤ 1 + Generated.soko3_2Potential.boulder 209 - Generated.soko3_2Potential.boulder 210 + bonus 210 (change p 210 (some 209)) := by
  have certified := compare9360 p (guard958 p guard)
  change d134 p ≤ (4 : Int) + d134 (change p 210 (some 209))
  have normalized := agree134 _ _ (change_representative support p 210 (some 209) 10000 dummy_outside)
  rw [normalized]
  change d134 p ≤ (4 : Int) + d134 (change p 10000 none)
  rw [sub249]
  exact certified
theorem check958 (p : Pattern) : (!pushGuard support p 211 210 209 209 || decide (bonus 211 p ≤ 1 + Generated.soko3_2Potential.boulder 209 - Generated.soko3_2Potential.boulder 210 + bonus 210 (change p 210 (some 209)))) = true :=
  check_of_implication _ _ (bound958 p)
theorem guard959 (p : Pattern) (guard : walkGuard soko3_2.board support p 212 213 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound959 (p : Pattern) (guard : walkGuard soko3_2.board support p 212 213 .east = true) : bonus 212 p ≤ bonus 213 p := by
  have certified := compare0 p (guard959 p guard)
  simpa only [at212, at213, Int.zero_add] using certified
theorem check959 (p : Pattern) : (!walkGuard soko3_2.board support p 212 213 .east || decide (bonus 212 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound959 p)
end NetHack.Sokoban32Refined
