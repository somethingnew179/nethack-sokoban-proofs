import NetHack.Sokoban22Refined85.ActionBounds038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard936 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 226 .east = true) : d5502 p = 1 := by
  change (!(p 225) && !false && !false) = true at guard
  cases h225 : p 225
  all_goals simp [d0, d1, d5502, h225] at guard ⊢
theorem bound936 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 226 .east = true) : bonus 225 p ≤ bonus 226 p := by
  have certified := compare21634 p (guard936 p guard)
  simpa only [at225, at226, Int.zero_add] using certified
theorem check936 (p : Pattern) : (!walkGuard soko2_2.board support p 225 226 .east || decide (bonus 225 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound936 p)
theorem guard937 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 224 .west = true) : d5503 p = 1 := by
  change (!(p 225) && !(p 224) && !false) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5502, d5503, h224, h225] at guard ⊢
theorem bound937 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 224 .west = true) : bonus 225 p ≤ bonus 224 p := by
  have certified := compare22064 p (guard937 p guard)
  simpa only [at225, at224, Int.zero_add] using certified
theorem check937 (p : Pattern) : (!walkGuard soko2_2.board support p 225 224 .west || decide (bonus 225 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound937 p)
theorem guard938 (p : Pattern) (guard : pushGuard support p 225 224 223 223 = true) : d5538 p = 1 := by
  change (!(p 225) && (!true || (p 224)) && !false && (!false || false)) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5502, d5538, h224, h225] at guard ⊢
theorem bound938 (p : Pattern) (guard : pushGuard support p 225 224 223 223 = true) : bonus 225 p ≤ 1 + Generated.soko2_2Potential.boulder 223 - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some 223)) := by
  have certified := compare22552 p (guard938 p guard)
  change d2894 p ≤ (4 : Int) + d2502 (change p 224 (some 223))
  have normalized := agree2502 _ _ (change_representative support p 224 (some 223) 10000 dummy_outside)
  rw [normalized]
  change d2894 p ≤ (4 : Int) + d2502 (change p 224 none)
  rw [sub10413]
  exact certified
theorem check938 (p : Pattern) : (!pushGuard support p 225 224 223 223 || decide (bonus 225 p ≤ 1 + Generated.soko2_2Potential.boulder 223 - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some 223)))) = true :=
  check_of_implication _ _ (bound938 p)
theorem guard939 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 204 .northEast = true) : d5537 p = 1 := by
  change (!(p 225) && !(p 204) && !(true && true && false)) = true at guard
  cases h204 : p 204 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5502, d5537, h204, h225] at guard ⊢
theorem bound939 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 204 .northEast = true) : bonus 225 p ≤ bonus 204 p := by
  have certified := compare22959 p (guard939 p guard)
  simpa only [at225, at204, Int.zero_add] using certified
theorem check939 (p : Pattern) : (!walkGuard soko2_2.board support p 225 204 .northEast || decide (bonus 225 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound939 p)
theorem guard940 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 202 .northWest = true) : d5503 p = 1 := by
  change (!(p 225) && !false && !(true && true && (p 224))) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5502, d5503, h224, h225] at guard ⊢
theorem bound940 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 202 .northWest = true) : bonus 225 p ≤ bonus 202 p := by
  have certified := compare23361 p (guard940 p guard)
  simpa only [at225, at202, Int.zero_add] using certified
theorem check940 (p : Pattern) : (!walkGuard soko2_2.board support p 225 202 .northWest || decide (bonus 225 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound940 p)
theorem guard941 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 248 .southEast = true) : d5502 p = 1 := by
  change (!(p 225) && !false && !(true && (p 247) && false)) = true at guard
  cases h225 : p 225 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5502, h225, h247] at guard ⊢
theorem bound941 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 248 .southEast = true) : bonus 225 p ≤ bonus 248 p := by
  have certified := compare21634 p (guard941 p guard)
  simpa only [at225, at248, Int.zero_add] using certified
theorem check941 (p : Pattern) : (!walkGuard soko2_2.board support p 225 248 .southEast || decide (bonus 225 p ≤ bonus 248 p)) = true :=
  check_of_implication _ _ (bound941 p)
theorem guard942 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 246 .southWest = true) : d5855 p = 1 := by
  change (!(p 225) && !(p 246) && !(true && (p 247) && (p 224))) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225 <;> cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5268, d5843, d5847, d5851, d5854, d5855, h224, h225, h246, h247] at guard ⊢
theorem bound942 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 246 .southWest = true) : bonus 225 p ≤ bonus 246 p := by
  have certified := compare23869 p (guard942 p guard)
  simpa only [at225, at246, Int.zero_add] using certified
theorem check942 (p : Pattern) : (!walkGuard soko2_2.board support p 225 246 .southWest || decide (bonus 225 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound942 p)
theorem guard943 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 204 .north = true) : d4474 p = 1 := by
  change (!false && !(p 204) && !false) = true at guard
  cases h204 : p 204
  all_goals simp [d0, d1, d4474, h204] at guard ⊢
theorem bound943 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 204 .north = true) : bonus 226 p ≤ bonus 204 p := by
  have certified := compare24275 p (guard943 p guard)
  simpa only [at226, at204, Int.zero_add] using certified
theorem check943 (p : Pattern) : (!walkGuard soko2_2.board support p 226 204 .north || decide (bonus 226 p ≤ bonus 204 p)) = true :=
  check_of_implication _ _ (bound943 p)
theorem guard944 (p : Pattern) (guard : pushGuard support p 226 204 182 182 = true) : d4985 p = 1 := by
  change (!false && (!true || (p 204)) && !(p 182) && (!(p 182) || false)) = true at guard
  cases h182 : p 182 <;> cases h204 : p 204
  all_goals simp [d0, d1, d4473, d4985, h182, h204] at guard ⊢
theorem bound944 (p : Pattern) (guard : pushGuard support p 226 204 182 182 = true) : bonus 226 p ≤ 1 + Generated.soko2_2Potential.boulder 182 - Generated.soko2_2Potential.boulder 204 + bonus 204 (change p 204 (some 182)) := by
  have certified := compare24906 p (guard944 p guard)
  change d3224 p ≤ (2 : Int) + d2183 (change p 204 (some 182))
  have normalized := agree2183 _ _ (change_representative support p 204 (some 182) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (2 : Int) + d2183 (change p 204 (some 182))
  rw [sub10960]
  exact certified
theorem check944 (p : Pattern) : (!pushGuard support p 226 204 182 182 || decide (bonus 226 p ≤ 1 + Generated.soko2_2Potential.boulder 182 - Generated.soko2_2Potential.boulder 204 + bonus 204 (change p 204 (some 182)))) = true :=
  check_of_implication _ _ (bound944 p)
theorem guard945 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 248 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound945 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 248 .south = true) : bonus 226 p ≤ bonus 248 p := by
  have certified := compare24907 p (guard945 p guard)
  simpa only [at226, at248, Int.zero_add] using certified
theorem check945 (p : Pattern) : (!walkGuard soko2_2.board support p 226 248 .south || decide (bonus 226 p ≤ bonus 248 p)) = true :=
  check_of_implication _ _ (bound945 p)
theorem guard946 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 225 .west = true) : d5502 p = 1 := by
  change (!false && !(p 225) && !false) = true at guard
  cases h225 : p 225
  all_goals simp [d0, d1, d5502, h225] at guard ⊢
theorem bound946 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 225 .west = true) : bonus 226 p ≤ bonus 225 p := by
  have certified := compare25321 p (guard946 p guard)
  simpa only [at226, at225, Int.zero_add] using certified
theorem check946 (p : Pattern) : (!walkGuard soko2_2.board support p 226 225 .west || decide (bonus 226 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound946 p)
theorem guard947 (p : Pattern) (guard : pushGuard support p 226 225 224 224 = true) : d5540 p = 1 := by
  change (!false && (!true || (p 225)) && !(p 224) && (!(p 224) || false)) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5501, d5540, h224, h225] at guard ⊢
theorem bound947 (p : Pattern) (guard : pushGuard support p 226 225 224 224 = true) : bonus 226 p ≤ 1 + Generated.soko2_2Potential.boulder 224 - Generated.soko2_2Potential.boulder 225 + bonus 225 (change p 225 (some 224)) := by
  have certified := compare25820 p (guard947 p guard)
  change d3224 p ≤ (2 : Int) + d2894 (change p 225 (some 224))
  have normalized := agree2894 _ _ (change_representative support p 225 (some 224) 10000 dummy_outside)
  rw [normalized]
  change d3224 p ≤ (2 : Int) + d2894 (change p 225 (some 224))
  rw [sub11421]
  exact certified
theorem check947 (p : Pattern) : (!pushGuard support p 226 225 224 224 || decide (bonus 226 p ≤ 1 + Generated.soko2_2Potential.boulder 224 - Generated.soko2_2Potential.boulder 225 + bonus 225 (change p 225 (some 224)))) = true :=
  check_of_implication _ _ (bound947 p)
theorem guard948 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 249 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound948 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 249 .southEast = true) : bonus 226 p ≤ bonus 249 p := by
  have certified := compare24907 p (guard948 p guard)
  simpa only [at226, at249, Int.zero_add] using certified
theorem check948 (p : Pattern) : (!walkGuard soko2_2.board support p 226 249 .southEast || decide (bonus 226 p ≤ bonus 249 p)) = true :=
  check_of_implication _ _ (bound948 p)
theorem guard949 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 247 .southWest = true) : d5843 p = 1 := by
  change (!false && !(p 247) && !(true && false && (p 225))) = true at guard
  cases h225 : p 225 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, h225, h247] at guard ⊢
theorem bound949 (p : Pattern) (guard : walkGuard soko2_2.board support p 226 247 .southWest = true) : bonus 226 p ≤ bonus 247 p := by
  have certified := compare26330 p (guard949 p guard)
  simpa only [at226, at247, Int.zero_add] using certified
theorem check949 (p : Pattern) : (!walkGuard soko2_2.board support p 226 247 .southWest || decide (bonus 226 p ≤ bonus 247 p)) = true :=
  check_of_implication _ _ (bound949 p)
theorem guard950 (p : Pattern) (guard : walkGuard soko2_2.board support p 240 218 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound950 (p : Pattern) (guard : walkGuard soko2_2.board support p 240 218 .north = true) : bonus 240 p ≤ bonus 218 p := by
  have certified := compare1086 p (guard950 p guard)
  simpa only [at240, at218, Int.zero_add] using certified
theorem check950 (p : Pattern) : (!walkGuard soko2_2.board support p 240 218 .north || decide (bonus 240 p ≤ bonus 218 p)) = true :=
  check_of_implication _ _ (bound950 p)
theorem guard951 (p : Pattern) (guard : walkGuard soko2_2.board support p 240 262 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound951 (p : Pattern) (guard : walkGuard soko2_2.board support p 240 262 .south = true) : bonus 240 p ≤ bonus 262 p := by
  have certified := compare1086 p (guard951 p guard)
  simpa only [at240, at262, Int.zero_add] using certified
theorem check951 (p : Pattern) : (!walkGuard soko2_2.board support p 240 262 .south || decide (bonus 240 p ≤ bonus 262 p)) = true :=
  check_of_implication _ _ (bound951 p)
theorem guard952 (p : Pattern) (guard : walkGuard soko2_2.board support p 245 223 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound952 (p : Pattern) (guard : walkGuard soko2_2.board support p 245 223 .north = true) : bonus 245 p ≤ bonus 223 p := by
  have certified := compare0 p (guard952 p guard)
  simpa only [at245, at223, Int.zero_add] using certified
theorem check952 (p : Pattern) : (!walkGuard soko2_2.board support p 245 223 .north || decide (bonus 245 p ≤ bonus 223 p)) = true :=
  check_of_implication _ _ (bound952 p)
theorem guard953 (p : Pattern) (guard : pushGuard support p 245 223 201 201 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound953 (p : Pattern) (guard : pushGuard support p 245 223 201 201 = true) : bonus 245 p ≤ 1 + Generated.soko2_2Potential.boulder 201 - Generated.soko2_2Potential.boulder 223 + bonus 223 (change p 223 (some 201)) := by
  have certified := compare0 p (guard953 p guard)
  change d267 p ≤ (0 : Int) + d267 (change p 223 (some 201))
  have normalized := agree267 _ _ (change_representative support p 223 (some 201) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check953 (p : Pattern) : (!pushGuard support p 245 223 201 201 || decide (bonus 245 p ≤ 1 + Generated.soko2_2Potential.boulder 201 - Generated.soko2_2Potential.boulder 223 + bonus 223 (change p 223 (some 201)))) = true :=
  check_of_implication _ _ (bound953 p)
theorem guard954 (p : Pattern) (guard : walkGuard soko2_2.board support p 245 246 .east = true) : d5268 p = 1 := by
  change (!false && !(p 246) && !false) = true at guard
  cases h246 : p 246
  all_goals simp [d0, d1, d5268, h246] at guard ⊢
theorem bound954 (p : Pattern) (guard : walkGuard soko2_2.board support p 245 246 .east = true) : bonus 245 p ≤ bonus 246 p := by
  have certified := compare17975 p (guard954 p guard)
  simpa only [at245, at246, Int.zero_add] using certified
theorem check954 (p : Pattern) : (!walkGuard soko2_2.board support p 245 246 .east || decide (bonus 245 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound954 p)
theorem guard955 (p : Pattern) (guard : pushGuard support p 245 246 247 247 = true) : d6326 p = 1 := by
  change (!false && (!true || (p 246)) && !(p 247) && (!(p 247) || false)) = true at guard
  cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, d6326, h246, h247] at guard ⊢
theorem bound955 (p : Pattern) (guard : pushGuard support p 245 246 247 247 = true) : bonus 245 p ≤ 1 + Generated.soko2_2Potential.boulder 247 - Generated.soko2_2Potential.boulder 246 + bonus 246 (change p 246 (some 247)) := by
  have certified := compare26602 p (guard955 p guard)
  change d267 p ≤ (0 : Int) + d3539 (change p 246 (some 247))
  have normalized := agree3539 _ _ (change_representative support p 246 (some 247) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d3539 (change p 246 (some 247))
  rw [sub11749]
  exact certified
theorem check955 (p : Pattern) : (!pushGuard support p 245 246 247 247 || decide (bonus 245 p ≤ 1 + Generated.soko2_2Potential.boulder 247 - Generated.soko2_2Potential.boulder 246 + bonus 246 (change p 246 (some 247)))) = true :=
  check_of_implication _ _ (bound955 p)
theorem guard956 (p : Pattern) (guard : walkGuard soko2_2.board support p 245 224 .northEast = true) : d4902 p = 1 := by
  change (!false && !(p 224) && !(true && false && (p 246))) = true at guard
  cases h224 : p 224 <;> cases h246 : p 246
  all_goals simp [d0, d1, d4902, h224, h246] at guard ⊢
theorem bound956 (p : Pattern) (guard : walkGuard soko2_2.board support p 245 224 .northEast = true) : bonus 245 p ≤ bonus 224 p := by
  have certified := compare14527 p (guard956 p guard)
  simpa only [at245, at224, Int.zero_add] using certified
theorem check956 (p : Pattern) : (!walkGuard soko2_2.board support p 245 224 .northEast || decide (bonus 245 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound956 p)
theorem guard957 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 224 .north = true) : d5539 p = 1 := by
  change (!(p 246) && !(p 224) && !false) = true at guard
  cases h224 : p 224 <;> cases h246 : p 246
  all_goals simp [d0, d1, d5268, d5539, h224, h246] at guard ⊢
theorem bound957 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 224 .north = true) : bonus 246 p ≤ bonus 224 p := by
  have certified := compare26971 p (guard957 p guard)
  simpa only [at246, at224, Int.zero_add] using certified
theorem check957 (p : Pattern) : (!walkGuard soko2_2.board support p 246 224 .north || decide (bonus 246 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound957 p)
theorem guard958 (p : Pattern) (guard : pushGuard support p 246 224 202 202 = true) : d5269 p = 1 := by
  change (!(p 246) && (!true || (p 224)) && !false && (!false || false)) = true at guard
  cases h224 : p 224 <;> cases h246 : p 246
  all_goals simp [d0, d1, d5268, d5269, h224, h246] at guard ⊢
theorem bound958 (p : Pattern) (guard : pushGuard support p 246 224 202 202 = true) : bonus 246 p ≤ 1 + Generated.soko2_2Potential.boulder 202 - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some 202)) := by
  have certified := compare27317 p (guard958 p guard)
  change d3539 p ≤ (2 : Int) + d2502 (change p 224 (some 202))
  have normalized := agree2502 _ _ (change_representative support p 224 (some 202) 10000 dummy_outside)
  rw [normalized]
  change d3539 p ≤ (2 : Int) + d2502 (change p 224 none)
  rw [sub10413]
  exact certified
theorem check958 (p : Pattern) : (!pushGuard support p 246 224 202 202 || decide (bonus 246 p ≤ 1 + Generated.soko2_2Potential.boulder 202 - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some 202)))) = true :=
  check_of_implication _ _ (bound958 p)
theorem guard959 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 247 .east = true) : d5847 p = 1 := by
  change (!(p 246) && !(p 247) && !false) = true at guard
  cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, d5847, h246, h247] at guard ⊢
theorem bound959 (p : Pattern) (guard : walkGuard soko2_2.board support p 246 247 .east = true) : bonus 246 p ≤ bonus 247 p := by
  have certified := compare27864 p (guard959 p guard)
  simpa only [at246, at247, Int.zero_add] using certified
theorem check959 (p : Pattern) : (!walkGuard soko2_2.board support p 246 247 .east || decide (bonus 246 p ≤ bonus 247 p)) = true :=
  check_of_implication _ _ (bound959 p)
end NetHack.Sokoban22Refined85
