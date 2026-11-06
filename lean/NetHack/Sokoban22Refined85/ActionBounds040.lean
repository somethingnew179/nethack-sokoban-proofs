import NetHack.Sokoban22Refined85.ActionBounds039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard960 (p : Pattern) (guard : pushGuard support p 246 247 248 248 = true) : d6558 p = 1 := by
  change (!(p 246) && (!true || (p 247)) && !false && (!false || false)) = true at guard
  cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5842, d6558, h246, h247] at guard ⊢
theorem bound960 (p : Pattern) (guard : pushGuard support p 246 247 248 248 = true) : bonus 246 p ≤ 1 + Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.boulder 247 + bonus 247 (change p 247 (some 248)) := by
  have certified := compare28429 p (guard960 p guard)
  change d3539 p ≤ (0 : Int) + d4036 (change p 247 (some 248))
  have normalized := agree4036 _ _ (change_representative support p 247 (some 248) 10000 dummy_outside)
  rw [normalized]
  change d3539 p ≤ (0 : Int) + d4036 (change p 247 none)
  rw [sub12287]
  exact certified
theorem check960 (p : Pattern) : (!pushGuard support p 246 247 248 248 || decide (bonus 246 p ≤ 1 + Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.boulder 247 + bonus 247 (change p 247 (some 248)))) = true :=
  check_of_implication _ _ (bound960 p)
theorem guard961 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 245 .west = true) : d5268 p = 1 := by
  change (!(p 246) && !false && !false) = true at guard
  cases h246 : p 246
  all_goals simp [d0, d1, d5268, h246] at guard ⊢
theorem bound961 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 245 .west = true) : bonus 246 p ≤ bonus 245 p := by
  have certified := compare28720 p (guard961 p guard)
  simpa only [at246, at245, Int.zero_add] using certified
theorem check961 (p : Pattern) : (!walkGuard soko2_2.board support p 246 245 .west || decide (bonus 246 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound961 p)
theorem guard962 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 225 .northEast = true) : d5855 p = 1 := by
  change (!(p 246) && !(p 225) && !(true && (p 224) && (p 247))) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225 <;> cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5268, d5843, d5847, d5851, d5854, d5855, h224, h225, h246, h247] at guard ⊢
theorem bound962 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 225 .northEast = true) : bonus 246 p ≤ bonus 225 p := by
  have certified := compare29203 p (guard962 p guard)
  simpa only [at246, at225, Int.zero_add] using certified
theorem check962 (p : Pattern) : (!walkGuard soko2_2.board support p 246 225 .northEast || decide (bonus 246 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound962 p)
theorem guard963 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 223 .northWest = true) : d5268 p = 1 := by
  change (!(p 246) && !false && !(true && (p 224) && false)) = true at guard
  cases h224 : p 224 <;> cases h246 : p 246
  all_goals simp [d0, d1, d5268, h224, h246] at guard ⊢
theorem bound963 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 223 .northWest = true) : bonus 246 p ≤ bonus 223 p := by
  have certified := compare28720 p (guard963 p guard)
  simpa only [at246, at223, Int.zero_add] using certified
theorem check963 (p : Pattern) : (!walkGuard soko2_2.board support p 246 223 .northWest || decide (bonus 246 p ≤ bonus 223 p)) = true :=
  check_of_implication _ _ (bound963 p)
theorem guard964 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 225 .north = true) : d5850 p = 1 := by
  change (!(p 247) && !(p 225) && !false) = true at guard
  cases h225 : p 225 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, d5850, h225, h247] at guard ⊢
theorem bound964 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 225 .north = true) : bonus 247 p ≤ bonus 225 p := by
  have certified := compare29807 p (guard964 p guard)
  simpa only [at247, at225, Int.zero_add] using certified
theorem check964 (p : Pattern) : (!walkGuard soko2_2.board support p 247 225 .north || decide (bonus 247 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound964 p)
theorem guard965 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 248 .east = true) : d5843 p = 1 := by
  change (!(p 247) && !false && !false) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound965 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 248 .east = true) : bonus 247 p ≤ bonus 248 p := by
  have certified := compare30309 p (guard965 p guard)
  simpa only [at247, at248, Int.zero_add] using certified
theorem check965 (p : Pattern) : (!walkGuard soko2_2.board support p 247 248 .east || decide (bonus 247 p ≤ bonus 248 p)) = true :=
  check_of_implication _ _ (bound965 p)
theorem guard966 (p : Pattern) (guard : pushGuard support p 247 248 249 250 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound966 (p : Pattern) (guard : pushGuard support p 247 248 249 250 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 250 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard966 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check966 (p : Pattern) : (!pushGuard support p 247 248 249 250 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 250 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound966 p)
theorem guard967 (p : Pattern) (guard : pushGuard support p 247 248 249 251 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound967 (p : Pattern) (guard : pushGuard support p 247 248 249 251 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 251 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard967 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check967 (p : Pattern) : (!pushGuard support p 247 248 249 251 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 251 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound967 p)
theorem guard968 (p : Pattern) (guard : pushGuard support p 247 248 249 252 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound968 (p : Pattern) (guard : pushGuard support p 247 248 249 252 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 252 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard968 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check968 (p : Pattern) : (!pushGuard support p 247 248 249 252 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 252 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound968 p)
theorem guard969 (p : Pattern) (guard : pushGuard support p 247 248 249 253 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound969 (p : Pattern) (guard : pushGuard support p 247 248 249 253 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 253 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard969 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check969 (p : Pattern) : (!pushGuard support p 247 248 249 253 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 253 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound969 p)
theorem guard970 (p : Pattern) (guard : pushGuard support p 247 248 249 254 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound970 (p : Pattern) (guard : pushGuard support p 247 248 249 254 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 254 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard970 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check970 (p : Pattern) : (!pushGuard support p 247 248 249 254 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 254 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound970 p)
theorem guard971 (p : Pattern) (guard : pushGuard support p 247 248 249 255 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound971 (p : Pattern) (guard : pushGuard support p 247 248 249 255 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 255 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard971 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check971 (p : Pattern) : (!pushGuard support p 247 248 249 255 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 255 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound971 p)
theorem guard972 (p : Pattern) (guard : pushGuard support p 247 248 249 256 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound972 (p : Pattern) (guard : pushGuard support p 247 248 249 256 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 256 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard972 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check972 (p : Pattern) : (!pushGuard support p 247 248 249 256 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 256 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound972 p)
theorem guard973 (p : Pattern) (guard : pushGuard support p 247 248 249 257 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound973 (p : Pattern) (guard : pushGuard support p 247 248 249 257 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 257 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard973 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check973 (p : Pattern) : (!pushGuard support p 247 248 249 257 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 257 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound973 p)
theorem guard974 (p : Pattern) (guard : pushGuard support p 247 248 249 258 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound974 (p : Pattern) (guard : pushGuard support p 247 248 249 258 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 258 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard974 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check974 (p : Pattern) : (!pushGuard support p 247 248 249 258 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 258 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound974 p)
theorem guard975 (p : Pattern) (guard : pushGuard support p 247 248 249 259 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound975 (p : Pattern) (guard : pushGuard support p 247 248 249 259 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 259 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard975 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check975 (p : Pattern) : (!pushGuard support p 247 248 249 259 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 259 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound975 p)
theorem guard976 (p : Pattern) (guard : pushGuard support p 247 248 249 260 = true) : d5843 p = 1 := by
  change (!(p 247) && (!false || false) && !false && (!false || false)) = true at guard
  cases h247 : p 247
  all_goals simp [d0, d1, d5843, h247] at guard ⊢
theorem bound976 (p : Pattern) (guard : pushGuard support p 247 248 249 260 = true) : bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 260 + bonus 248 (change p 248 none) := by
  have certified := compare30309 p (guard976 p guard)
  change d4036 p ≤ (0 : Int) + d3224 (change p 248 none)
  have normalized := agree3224 _ _ (change_representative support p 248 none 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check976 (p : Pattern) : (!pushGuard support p 247 248 249 260 || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole 260 + bonus 248 (change p 248 none))) = true :=
  check_of_implication _ _ (bound976 p)
theorem guard977 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 246 .west = true) : d5847 p = 1 := by
  change (!(p 247) && !(p 246) && !false) = true at guard
  cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, d5847, h246, h247] at guard ⊢
theorem bound977 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 246 .west = true) : bonus 247 p ≤ bonus 246 p := by
  have certified := compare30851 p (guard977 p guard)
  simpa only [at247, at246, Int.zero_add] using certified
theorem check977 (p : Pattern) : (!walkGuard soko2_2.board support p 247 246 .west || decide (bonus 247 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound977 p)
theorem guard978 (p : Pattern) (guard : pushGuard support p 247 246 245 245 = true) : d6326 p = 1 := by
  change (!(p 247) && (!true || (p 246)) && !false && (!false || false)) = true at guard
  cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, d6326, h246, h247] at guard ⊢
theorem bound978 (p : Pattern) (guard : pushGuard support p 247 246 245 245 = true) : bonus 247 p ≤ 1 + Generated.soko2_2Potential.boulder 245 - Generated.soko2_2Potential.boulder 246 + bonus 246 (change p 246 (some 245)) := by
  have certified := compare31490 p (guard978 p guard)
  change d4036 p ≤ (9 : Int) + d3539 (change p 246 (some 245))
  have normalized := agree3539 _ _ (change_representative support p 246 (some 245) 10000 dummy_outside)
  rw [normalized]
  change d4036 p ≤ (9 : Int) + d3539 (change p 246 none)
  rw [sub12615]
  exact certified
theorem check978 (p : Pattern) : (!pushGuard support p 247 246 245 245 || decide (bonus 247 p ≤ 1 + Generated.soko2_2Potential.boulder 245 - Generated.soko2_2Potential.boulder 246 + bonus 246 (change p 246 (some 245)))) = true :=
  check_of_implication _ _ (bound978 p)
theorem guard979 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 226 .northEast = true) : d5843 p = 1 := by
  change (!(p 247) && !false && !(true && (p 225) && false)) = true at guard
  cases h225 : p 225 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, h225, h247] at guard ⊢
theorem bound979 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 226 .northEast = true) : bonus 247 p ≤ bonus 226 p := by
  have certified := compare30309 p (guard979 p guard)
  simpa only [at247, at226, Int.zero_add] using certified
theorem check979 (p : Pattern) : (!walkGuard soko2_2.board support p 247 226 .northEast || decide (bonus 247 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound979 p)
theorem guard980 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 224 .northWest = true) : d5849 p = 1 := by
  change (!(p 247) && !(p 224) && !(true && (p 225) && (p 246))) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225 <;> cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, d5847, d5848, d5849, h224, h225, h246, h247] at guard ⊢
theorem bound980 (p : Pattern) (guard : walkGuard soko2_2.board support p 247 224 .northWest = true) : bonus 247 p ≤ bonus 224 p := by
  have certified := compare32088 p (guard980 p guard)
  simpa only [at247, at224, Int.zero_add] using certified
theorem check980 (p : Pattern) : (!walkGuard soko2_2.board support p 247 224 .northWest || decide (bonus 247 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound980 p)
theorem guard981 (p : Pattern) (guard : walkGuard soko2_2.board support p 248 226 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound981 (p : Pattern) (guard : walkGuard soko2_2.board support p 248 226 .north = true) : bonus 248 p ≤ bonus 226 p := by
  have certified := compare24907 p (guard981 p guard)
  simpa only [at248, at226, Int.zero_add] using certified
theorem check981 (p : Pattern) : (!walkGuard soko2_2.board support p 248 226 .north || decide (bonus 248 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound981 p)
theorem guard982 (p : Pattern) (guard : pushGuard support p 248 226 204 204 = true) : d4474 p = 1 := by
  change (!false && (!false || false) && !(p 204) && (!(p 204) || false)) = true at guard
  cases h204 : p 204
  all_goals simp [d0, d1, d4474, h204] at guard ⊢
theorem bound982 (p : Pattern) (guard : pushGuard support p 248 226 204 204 = true) : bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder 204 - Generated.soko2_2Potential.boulder 226 + bonus 226 (change p 226 (some 204)) := by
  have certified := compare32655 p (guard982 p guard)
  change d3224 p ≤ (2 : Int) + d3224 (change p 226 (some 204))
  have normalized := agree3224 _ _ (change_representative support p 226 (some 204) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (2 : Int) + d3224 (change p 10000 (some 204))
  rw [sub13118]
  exact certified
theorem check982 (p : Pattern) : (!pushGuard support p 248 226 204 204 || decide (bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder 204 - Generated.soko2_2Potential.boulder 226 + bonus 226 (change p 226 (some 204)))) = true :=
  check_of_implication _ _ (bound982 p)
theorem guard983 (p : Pattern) (guard : walkGuard soko2_2.board support p 248 249 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound983 (p : Pattern) (guard : walkGuard soko2_2.board support p 248 249 .east = true) : bonus 248 p ≤ bonus 249 p := by
  have certified := compare24907 p (guard983 p guard)
  simpa only [at248, at249, Int.zero_add] using certified
theorem check983 (p : Pattern) : (!walkGuard soko2_2.board support p 248 249 .east || decide (bonus 248 p ≤ bonus 249 p)) = true :=
  check_of_implication _ _ (bound983 p)
end NetHack.Sokoban22Refined85
