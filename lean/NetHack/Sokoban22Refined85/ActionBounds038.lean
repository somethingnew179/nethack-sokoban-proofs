import NetHack.Sokoban22Refined85.ActionBounds037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard912 (p : Pattern) (guard : walkGuard soko2_2.board support p 216 194 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound912 (p : Pattern) (guard : walkGuard soko2_2.board support p 216 194 .north = true) : bonus 216 p ≤ bonus 194 p := by
  have certified := compare1086 p (guard912 p guard)
  simpa only [at216, at194, Int.zero_add] using certified
theorem check912 (p : Pattern) : (!walkGuard soko2_2.board support p 216 194 .north || decide (bonus 216 p ≤ bonus 194 p)) = true :=
  check_of_implication _ _ (bound912 p)
theorem guard913 (p : Pattern) (guard : pushGuard support p 216 194 172 172 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound913 (p : Pattern) (guard : pushGuard support p 216 194 172 172 = true) : bonus 216 p ≤ 1 + Generated.soko2_2Potential.boulder 172 - Generated.soko2_2Potential.boulder 194 + bonus 194 (change p 194 (some 172)) := by
  have certified := compare1087 p (guard913 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 194 (some 172))
  have normalized := agree0 _ _ (change_representative support p 194 (some 172) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check913 (p : Pattern) : (!pushGuard support p 216 194 172 172 || decide (bonus 216 p ≤ 1 + Generated.soko2_2Potential.boulder 172 - Generated.soko2_2Potential.boulder 194 + bonus 194 (change p 194 (some 172)))) = true :=
  check_of_implication _ _ (bound913 p)
theorem guard914 (p : Pattern) (guard : walkGuard soko2_2.board support p 216 215 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound914 (p : Pattern) (guard : walkGuard soko2_2.board support p 216 215 .west = true) : bonus 216 p ≤ bonus 215 p := by
  have certified := compare1086 p (guard914 p guard)
  simpa only [at216, at215, Int.zero_add] using certified
theorem check914 (p : Pattern) : (!walkGuard soko2_2.board support p 216 215 .west || decide (bonus 216 p ≤ bonus 215 p)) = true :=
  check_of_implication _ _ (bound914 p)
theorem guard915 (p : Pattern) (guard : pushGuard support p 216 215 214 214 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound915 (p : Pattern) (guard : pushGuard support p 216 215 214 214 = true) : bonus 216 p ≤ 1 + Generated.soko2_2Potential.boulder 214 - Generated.soko2_2Potential.boulder 215 + bonus 215 (change p 215 (some 214)) := by
  have certified := compare1087 p (guard915 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 215 (some 214))
  have normalized := agree0 _ _ (change_representative support p 215 (some 214) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check915 (p : Pattern) : (!pushGuard support p 216 215 214 214 || decide (bonus 216 p ≤ 1 + Generated.soko2_2Potential.boulder 214 - Generated.soko2_2Potential.boulder 215 + bonus 215 (change p 215 (some 214)))) = true :=
  check_of_implication _ _ (bound915 p)
theorem guard916 (p : Pattern) (guard : walkGuard soko2_2.board support p 216 193 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound916 (p : Pattern) (guard : walkGuard soko2_2.board support p 216 193 .northWest = true) : bonus 216 p ≤ bonus 193 p := by
  have certified := compare1086 p (guard916 p guard)
  simpa only [at216, at193, Int.zero_add] using certified
theorem check916 (p : Pattern) : (!walkGuard soko2_2.board support p 216 193 .northWest || decide (bonus 216 p ≤ bonus 193 p)) = true :=
  check_of_implication _ _ (bound916 p)
theorem guard917 (p : Pattern) (guard : walkGuard soko2_2.board support p 218 240 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound917 (p : Pattern) (guard : walkGuard soko2_2.board support p 218 240 .south = true) : bonus 218 p ≤ bonus 240 p := by
  have certified := compare1086 p (guard917 p guard)
  simpa only [at218, at240, Int.zero_add] using certified
theorem check917 (p : Pattern) : (!walkGuard soko2_2.board support p 218 240 .south || decide (bonus 218 p ≤ bonus 240 p)) = true :=
  check_of_implication _ _ (bound917 p)
theorem guard918 (p : Pattern) (guard : pushGuard support p 218 240 262 262 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound918 (p : Pattern) (guard : pushGuard support p 218 240 262 262 = true) : bonus 218 p ≤ 1 + Generated.soko2_2Potential.boulder 262 - Generated.soko2_2Potential.boulder 240 + bonus 240 (change p 240 (some 262)) := by
  have certified := compare1087 p (guard918 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 240 (some 262))
  have normalized := agree0 _ _ (change_representative support p 240 (some 262) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check918 (p : Pattern) : (!pushGuard support p 218 240 262 262 || decide (bonus 218 p ≤ 1 + Generated.soko2_2Potential.boulder 262 - Generated.soko2_2Potential.boulder 240 + bonus 240 (change p 240 (some 262)))) = true :=
  check_of_implication _ _ (bound918 p)
theorem guard919 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 201 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound919 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 201 .north = true) : bonus 223 p ≤ bonus 201 p := by
  have certified := compare0 p (guard919 p guard)
  simpa only [at223, at201, Int.zero_add] using certified
theorem check919 (p : Pattern) : (!walkGuard soko2_2.board support p 223 201 .north || decide (bonus 223 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound919 p)
theorem guard920 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 245 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound920 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 245 .south = true) : bonus 223 p ≤ bonus 245 p := by
  have certified := compare0 p (guard920 p guard)
  simpa only [at223, at245, Int.zero_add] using certified
theorem check920 (p : Pattern) : (!walkGuard soko2_2.board support p 223 245 .south || decide (bonus 223 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound920 p)
theorem guard921 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 224 .east = true) : d4902 p = 1 := by
  change (!false && !(p 224) && !false) = true at guard
  cases h224 : p 224
  all_goals simp [d0, d1, d4902, h224] at guard ⊢
theorem bound921 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 224 .east = true) : bonus 223 p ≤ bonus 224 p := by
  have certified := compare14527 p (guard921 p guard)
  simpa only [at223, at224, Int.zero_add] using certified
theorem check921 (p : Pattern) : (!walkGuard soko2_2.board support p 223 224 .east || decide (bonus 223 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound921 p)
theorem guard922 (p : Pattern) (guard : pushGuard support p 223 224 225 225 = true) : d5538 p = 1 := by
  change (!false && (!true || (p 224)) && !(p 225) && (!(p 225) || false)) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5502, d5538, h224, h225] at guard ⊢
theorem bound922 (p : Pattern) (guard : pushGuard support p 223 224 225 225 = true) : bonus 223 p ≤ 1 + Generated.soko2_2Potential.boulder 225 - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some 225)) := by
  have certified := compare17641 p (guard922 p guard)
  change d267 p ≤ (0 : Int) + d2502 (change p 224 (some 225))
  have normalized := agree2502 _ _ (change_representative support p 224 (some 225) 10000 dummy_outside)
  rw [normalized]
  change d267 p ≤ (0 : Int) + d2502 (change p 224 (some 225))
  rw [sub9590]
  exact certified
theorem check922 (p : Pattern) : (!pushGuard support p 223 224 225 225 || decide (bonus 223 p ≤ 1 + Generated.soko2_2Potential.boulder 225 - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some 225)))) = true :=
  check_of_implication _ _ (bound922 p)
theorem guard923 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 202 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && (p 224))) = true at guard
  cases h224 : p 224
  all_goals simp [d1, h224] at guard ⊢
theorem bound923 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 202 .northEast = true) : bonus 223 p ≤ bonus 202 p := by
  have certified := compare0 p (guard923 p guard)
  simpa only [at223, at202, Int.zero_add] using certified
theorem check923 (p : Pattern) : (!walkGuard soko2_2.board support p 223 202 .northEast || decide (bonus 223 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound923 p)
theorem guard924 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 200 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && true)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound924 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 200 .northWest = true) : bonus 223 p ≤ bonus 200 p := by
  have certified := compare0 p (guard924 p guard)
  simpa only [at223, at200, Int.zero_add] using certified
theorem check924 (p : Pattern) : (!walkGuard soko2_2.board support p 223 200 .northWest || decide (bonus 223 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound924 p)
theorem guard925 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 246 .southEast = true) : d5268 p = 1 := by
  change (!false && !(p 246) && !(true && false && (p 224))) = true at guard
  cases h224 : p 224 <;> cases h246 : p 246
  all_goals simp [d0, d1, d5268, h224, h246] at guard ⊢
theorem bound925 (p : Pattern) (guard : walkGuard soko2_2.board support p 223 246 .southEast = true) : bonus 223 p ≤ bonus 246 p := by
  have certified := compare17975 p (guard925 p guard)
  simpa only [at223, at246, Int.zero_add] using certified
theorem check925 (p : Pattern) : (!walkGuard soko2_2.board support p 223 246 .southEast || decide (bonus 223 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound925 p)
theorem guard926 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 202 .north = true) : d4902 p = 1 := by
  change (!(p 224) && !false && !false) = true at guard
  cases h224 : p 224
  all_goals simp [d0, d1, d4902, h224] at guard ⊢
theorem bound926 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 202 .north = true) : bonus 224 p ≤ bonus 202 p := by
  have certified := compare18302 p (guard926 p guard)
  simpa only [at224, at202, Int.zero_add] using certified
theorem check926 (p : Pattern) : (!walkGuard soko2_2.board support p 224 202 .north || decide (bonus 224 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound926 p)
theorem guard927 (p : Pattern) (guard : pushGuard support p 224 202 180 180 = true) : d4902 p = 1 := by
  change (!(p 224) && (!false || false) && !false && (!false || false)) = true at guard
  cases h224 : p 224
  all_goals simp [d0, d1, d4902, h224] at guard ⊢
theorem bound927 (p : Pattern) (guard : pushGuard support p 224 202 180 180 = true) : bonus 224 p ≤ 1 + Generated.soko2_2Potential.boulder 180 - Generated.soko2_2Potential.boulder 202 + bonus 202 (change p 202 (some 180)) := by
  have certified := compare18630 p (guard927 p guard)
  change d2502 p ≤ (2 : Int) + d267 (change p 202 (some 180))
  have normalized := agree267 _ _ (change_representative support p 202 (some 180) 10000 dummy_outside)
  rw [normalized]
  change d2502 p ≤ (2 : Int) + d267 (change p 10000 none)
  rw [sub267]
  exact certified
theorem check927 (p : Pattern) : (!pushGuard support p 224 202 180 180 || decide (bonus 224 p ≤ 1 + Generated.soko2_2Potential.boulder 180 - Generated.soko2_2Potential.boulder 202 + bonus 202 (change p 202 (some 180)))) = true :=
  check_of_implication _ _ (bound927 p)
theorem guard928 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 246 .south = true) : d5539 p = 1 := by
  change (!(p 224) && !(p 246) && !false) = true at guard
  cases h224 : p 224 <;> cases h246 : p 246
  all_goals simp [d0, d1, d5268, d5539, h224, h246] at guard ⊢
theorem bound928 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 246 .south = true) : bonus 224 p ≤ bonus 246 p := by
  have certified := compare18970 p (guard928 p guard)
  simpa only [at224, at246, Int.zero_add] using certified
theorem check928 (p : Pattern) : (!walkGuard soko2_2.board support p 224 246 .south || decide (bonus 224 p ≤ bonus 246 p)) = true :=
  check_of_implication _ _ (bound928 p)
theorem guard929 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 225 .east = true) : d5503 p = 1 := by
  change (!(p 224) && !(p 225) && !false) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5502, d5503, h224, h225] at guard ⊢
theorem bound929 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 225 .east = true) : bonus 224 p ≤ bonus 225 p := by
  have certified := compare19400 p (guard929 p guard)
  simpa only [at224, at225, Int.zero_add] using certified
theorem check929 (p : Pattern) : (!walkGuard soko2_2.board support p 224 225 .east || decide (bonus 224 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound929 p)
theorem guard930 (p : Pattern) (guard : pushGuard support p 224 225 226 226 = true) : d5540 p = 1 := by
  change (!(p 224) && (!true || (p 225)) && !false && (!false || false)) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5501, d5540, h224, h225] at guard ⊢
theorem bound930 (p : Pattern) (guard : pushGuard support p 224 225 226 226 = true) : bonus 224 p ≤ 1 + Generated.soko2_2Potential.boulder 226 - Generated.soko2_2Potential.boulder 225 + bonus 225 (change p 225 (some 226)) := by
  have certified := compare19823 p (guard930 p guard)
  change d2502 p ≤ (0 : Int) + d2894 (change p 225 (some 226))
  have normalized := agree2894 _ _ (change_representative support p 225 (some 226) 10000 dummy_outside)
  rw [normalized]
  change d2502 p ≤ (0 : Int) + d2894 (change p 225 none)
  rw [sub10057]
  exact certified
theorem check930 (p : Pattern) : (!pushGuard support p 224 225 226 226 || decide (bonus 224 p ≤ 1 + Generated.soko2_2Potential.boulder 226 - Generated.soko2_2Potential.boulder 225 + bonus 225 (change p 225 (some 226)))) = true :=
  check_of_implication _ _ (bound930 p)
theorem guard931 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 223 .west = true) : d4902 p = 1 := by
  change (!(p 224) && !false && !false) = true at guard
  cases h224 : p 224
  all_goals simp [d0, d1, d4902, h224] at guard ⊢
theorem bound931 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 223 .west = true) : bonus 224 p ≤ bonus 223 p := by
  have certified := compare18302 p (guard931 p guard)
  simpa only [at224, at223, Int.zero_add] using certified
theorem check931 (p : Pattern) : (!walkGuard soko2_2.board support p 224 223 .west || decide (bonus 224 p ≤ bonus 223 p)) = true :=
  check_of_implication _ _ (bound931 p)
theorem guard932 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 201 .northWest = true) : d4902 p = 1 := by
  change (!(p 224) && !false && !(true && false && false)) = true at guard
  cases h224 : p 224
  all_goals simp [d0, d1, d4902, h224] at guard ⊢
theorem bound932 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 201 .northWest = true) : bonus 224 p ≤ bonus 201 p := by
  have certified := compare18302 p (guard932 p guard)
  simpa only [at224, at201, Int.zero_add] using certified
theorem check932 (p : Pattern) : (!walkGuard soko2_2.board support p 224 201 .northWest || decide (bonus 224 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound932 p)
theorem guard933 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 247 .southEast = true) : d5849 p = 1 := by
  change (!(p 224) && !(p 247) && !(true && (p 246) && (p 225))) = true at guard
  cases h224 : p 224 <;> cases h225 : p 225 <;> cases h246 : p 246 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, d5847, d5848, d5849, h224, h225, h246, h247] at guard ⊢
theorem bound933 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 247 .southEast = true) : bonus 224 p ≤ bonus 247 p := by
  have certified := compare20507 p (guard933 p guard)
  simpa only [at224, at247, Int.zero_add] using certified
theorem check933 (p : Pattern) : (!walkGuard soko2_2.board support p 224 247 .southEast || decide (bonus 224 p ≤ bonus 247 p)) = true :=
  check_of_implication _ _ (bound933 p)
theorem guard934 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 245 .southWest = true) : d4902 p = 1 := by
  change (!(p 224) && !false && !(true && (p 246) && false)) = true at guard
  cases h224 : p 224 <;> cases h246 : p 246
  all_goals simp [d0, d1, d4902, h224, h246] at guard ⊢
theorem bound934 (p : Pattern) (guard : walkGuard soko2_2.board support p 224 245 .southWest = true) : bonus 224 p ≤ bonus 245 p := by
  have certified := compare18302 p (guard934 p guard)
  simpa only [at224, at245, Int.zero_add] using certified
theorem check934 (p : Pattern) : (!walkGuard soko2_2.board support p 224 245 .southWest || decide (bonus 224 p ≤ bonus 245 p)) = true :=
  check_of_implication _ _ (bound934 p)
theorem guard935 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 247 .south = true) : d5850 p = 1 := by
  change (!(p 225) && !(p 247) && !false) = true at guard
  cases h225 : p 225 <;> cases h247 : p 247
  all_goals simp [d0, d1, d5843, d5850, h225, h247] at guard ⊢
theorem bound935 (p : Pattern) (guard : walkGuard soko2_2.board support p 225 247 .south = true) : bonus 225 p ≤ bonus 247 p := by
  have certified := compare21086 p (guard935 p guard)
  simpa only [at225, at247, Int.zero_add] using certified
theorem check935 (p : Pattern) : (!walkGuard soko2_2.board support p 225 247 .south || decide (bonus 225 p ≤ bonus 247 p)) = true :=
  check_of_implication _ _ (bound935 p)
end NetHack.Sokoban22Refined85
