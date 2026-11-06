import NetHack.Sokoban22Refined85.ActionBounds035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard864 (p : Pattern) (guard : pushGuard support p 204 182 160 160 = true) : d4476 p = 1 := by
  change (!(p 204) && (!true || (p 182)) && !(p 160) && (!(p 160) || false)) = true at guard
  cases h160 : p 160 <;> cases h182 : p 182 <;> cases h204 : p 204
  all_goals simp [d0, d1, d4474, d4475, d4476, h160, h182, h204] at guard ⊢
theorem bound864 (p : Pattern) (guard : pushGuard support p 204 182 160 160 = true) : bonus 204 p ≤ 1 + Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.boulder 182 + bonus 182 (change p 182 (some 160)) := by
  have certified := compare16327 p (guard864 p guard)
  change d2183 p ≤ (2 : Int) + d1681 (change p 182 (some 160))
  have normalized := agree1681 _ _ (change_representative support p 182 (some 160) 10000 dummy_outside)
  rw [normalized]
  change d2183 p ≤ (2 : Int) + d1681 (change p 182 (some 160))
  rw [sub8734]
  exact certified
theorem check864 (p : Pattern) : (!pushGuard support p 204 182 160 160 || decide (bonus 204 p ≤ 1 + Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.boulder 182 + bonus 182 (change p 182 (some 160)))) = true :=
  check_of_implication _ _ (bound864 p)
theorem guard865 (p : Pattern) (guard : walkGuard soko2_2.board support p 204 226 .south = true) : d4474 p = 1 := by
  change (!(p 204) && !false && !false) = true at guard
  cases h204 : p 204
  all_goals simp [d0, d1, d4474, h204] at guard ⊢
theorem bound865 (p : Pattern) (guard : walkGuard soko2_2.board support p 204 226 .south = true) : bonus 204 p ≤ bonus 226 p := by
  have certified := compare16743 p (guard865 p guard)
  simpa only [at204, at226, Int.zero_add] using certified
theorem check865 (p : Pattern) : (!walkGuard soko2_2.board support p 204 226 .south || decide (bonus 204 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound865 p)
theorem guard866 (p : Pattern) (guard : pushGuard support p 204 226 248 248 = true) : d4474 p = 1 := by
  change (!(p 204) && (!false || false) && !false && (!false || false)) = true at guard
  cases h204 : p 204
  all_goals simp [d0, d1, d4474, h204] at guard ⊢
theorem bound866 (p : Pattern) (guard : pushGuard support p 204 226 248 248 = true) : bonus 204 p ≤ 1 + Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.boulder 226 + bonus 226 (change p 226 (some 248)) := by
  have certified := compare16743 p (guard866 p guard)
  change d2183 p ≤ (0 : Int) + d3224 (change p 226 (some 248))
  have normalized := agree3224 _ _ (change_representative support p 226 (some 248) 10000 dummy_outside)
  rw [normalized]
  change d2183 p ≤ (0 : Int) + d3224 (change p 10000 none)
  rw [sub9234]
  exact certified
theorem check866 (p : Pattern) : (!pushGuard support p 204 226 248 248 || decide (bonus 204 p ≤ 1 + Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.boulder 226 + bonus 226 (change p 226 (some 248)))) = true :=
  check_of_implication _ _ (bound866 p)
theorem guard867 (p : Pattern) (guard : walkGuard soko2_2.board support p 204 181 .northWest = true) : d4967 p = 1 := by
  change (!(p 204) && !false && !(true && (p 182) && true)) = true at guard
  cases h182 : p 182 <;> cases h204 : p 204
  all_goals simp [d0, d1, d4474, d4967, h182, h204] at guard ⊢
theorem bound867 (p : Pattern) (guard : walkGuard soko2_2.board support p 204 181 .northWest = true) : bonus 204 p ≤ bonus 181 p := by
  have certified := compare17080 p (guard867 p guard)
  simpa only [at204, at181, Int.zero_add] using certified
theorem check867 (p : Pattern) : (!walkGuard soko2_2.board support p 204 181 .northWest || decide (bonus 204 p ≤ bonus 181 p)) = true :=
  check_of_implication _ _ (bound867 p)
theorem guard868 (p : Pattern) (guard : walkGuard soko2_2.board support p 204 225 .southWest = true) : d5537 p = 1 := by
  change (!(p 204) && !(p 225) && !(true && false && true)) = true at guard
  cases h204 : p 204 <;> cases h225 : p 225
  all_goals simp [d0, d1, d5502, d5537, h204, h225] at guard ⊢
theorem bound868 (p : Pattern) (guard : walkGuard soko2_2.board support p 204 225 .southWest = true) : bonus 204 p ≤ bonus 225 p := by
  have certified := compare17640 p (guard868 p guard)
  simpa only [at204, at225, Int.zero_add] using certified
theorem check868 (p : Pattern) : (!walkGuard soko2_2.board support p 204 225 .southWest || decide (bonus 204 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound868 p)
theorem guard869 (p : Pattern) (guard : walkGuard soko2_2.board support p 210 188 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound869 (p : Pattern) (guard : walkGuard soko2_2.board support p 210 188 .north = true) : bonus 210 p ≤ bonus 188 p := by
  have certified := compare1086 p (guard869 p guard)
  simpa only [at210, at188, Int.zero_add] using certified
theorem check869 (p : Pattern) : (!walkGuard soko2_2.board support p 210 188 .north || decide (bonus 210 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound869 p)
theorem guard870 (p : Pattern) (guard : pushGuard support p 210 188 166 166 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound870 (p : Pattern) (guard : pushGuard support p 210 188 166 166 = true) : bonus 210 p ≤ 1 + Generated.soko2_2Potential.boulder 166 - Generated.soko2_2Potential.boulder 188 + bonus 188 (change p 188 (some 166)) := by
  have certified := compare1087 p (guard870 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 188 (some 166))
  have normalized := agree0 _ _ (change_representative support p 188 (some 166) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check870 (p : Pattern) : (!pushGuard support p 210 188 166 166 || decide (bonus 210 p ≤ 1 + Generated.soko2_2Potential.boulder 166 - Generated.soko2_2Potential.boulder 188 + bonus 188 (change p 188 (some 166)))) = true :=
  check_of_implication _ _ (bound870 p)
theorem guard871 (p : Pattern) (guard : walkGuard soko2_2.board support p 210 211 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound871 (p : Pattern) (guard : walkGuard soko2_2.board support p 210 211 .east = true) : bonus 210 p ≤ bonus 211 p := by
  have certified := compare1086 p (guard871 p guard)
  simpa only [at210, at211, Int.zero_add] using certified
theorem check871 (p : Pattern) : (!walkGuard soko2_2.board support p 210 211 .east || decide (bonus 210 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound871 p)
theorem guard872 (p : Pattern) (guard : pushGuard support p 210 211 212 212 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound872 (p : Pattern) (guard : pushGuard support p 210 211 212 212 = true) : bonus 210 p ≤ 1 + Generated.soko2_2Potential.boulder 212 - Generated.soko2_2Potential.boulder 211 + bonus 211 (change p 211 (some 212)) := by
  have certified := compare1087 p (guard872 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 211 (some 212))
  have normalized := agree0 _ _ (change_representative support p 211 (some 212) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check872 (p : Pattern) : (!pushGuard support p 210 211 212 212 || decide (bonus 210 p ≤ 1 + Generated.soko2_2Potential.boulder 212 - Generated.soko2_2Potential.boulder 211 + bonus 211 (change p 211 (some 212)))) = true :=
  check_of_implication _ _ (bound872 p)
theorem guard873 (p : Pattern) (guard : walkGuard soko2_2.board support p 210 189 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound873 (p : Pattern) (guard : walkGuard soko2_2.board support p 210 189 .northEast = true) : bonus 210 p ≤ bonus 189 p := by
  have certified := compare1086 p (guard873 p guard)
  simpa only [at210, at189, Int.zero_add] using certified
theorem check873 (p : Pattern) : (!walkGuard soko2_2.board support p 210 189 .northEast || decide (bonus 210 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound873 p)
theorem guard874 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 189 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound874 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 189 .north = true) : bonus 211 p ≤ bonus 189 p := by
  have certified := compare1086 p (guard874 p guard)
  simpa only [at211, at189, Int.zero_add] using certified
theorem check874 (p : Pattern) : (!walkGuard soko2_2.board support p 211 189 .north || decide (bonus 211 p ≤ bonus 189 p)) = true :=
  check_of_implication _ _ (bound874 p)
theorem guard875 (p : Pattern) (guard : pushGuard support p 211 189 167 167 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound875 (p : Pattern) (guard : pushGuard support p 211 189 167 167 = true) : bonus 211 p ≤ 1 + Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some 167)) := by
  have certified := compare1087 p (guard875 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 189 (some 167))
  have normalized := agree0 _ _ (change_representative support p 189 (some 167) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check875 (p : Pattern) : (!pushGuard support p 211 189 167 167 || decide (bonus 211 p ≤ 1 + Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some 167)))) = true :=
  check_of_implication _ _ (bound875 p)
theorem guard876 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 212 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound876 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 212 .east = true) : bonus 211 p ≤ bonus 212 p := by
  have certified := compare1086 p (guard876 p guard)
  simpa only [at211, at212, Int.zero_add] using certified
theorem check876 (p : Pattern) : (!walkGuard soko2_2.board support p 211 212 .east || decide (bonus 211 p ≤ bonus 212 p)) = true :=
  check_of_implication _ _ (bound876 p)
theorem guard877 (p : Pattern) (guard : pushGuard support p 211 212 213 213 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound877 (p : Pattern) (guard : pushGuard support p 211 212 213 213 = true) : bonus 211 p ≤ 1 + Generated.soko2_2Potential.boulder 213 - Generated.soko2_2Potential.boulder 212 + bonus 212 (change p 212 (some 213)) := by
  have certified := compare1087 p (guard877 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 212 (some 213))
  have normalized := agree0 _ _ (change_representative support p 212 (some 213) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check877 (p : Pattern) : (!pushGuard support p 211 212 213 213 || decide (bonus 211 p ≤ 1 + Generated.soko2_2Potential.boulder 213 - Generated.soko2_2Potential.boulder 212 + bonus 212 (change p 212 (some 213)))) = true :=
  check_of_implication _ _ (bound877 p)
theorem guard878 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 210 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound878 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 210 .west = true) : bonus 211 p ≤ bonus 210 p := by
  have certified := compare1086 p (guard878 p guard)
  simpa only [at211, at210, Int.zero_add] using certified
theorem check878 (p : Pattern) : (!walkGuard soko2_2.board support p 211 210 .west || decide (bonus 211 p ≤ bonus 210 p)) = true :=
  check_of_implication _ _ (bound878 p)
theorem guard879 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 190 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound879 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 190 .northEast = true) : bonus 211 p ≤ bonus 190 p := by
  have certified := compare1086 p (guard879 p guard)
  simpa only [at211, at190, Int.zero_add] using certified
theorem check879 (p : Pattern) : (!walkGuard soko2_2.board support p 211 190 .northEast || decide (bonus 211 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound879 p)
theorem guard880 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 188 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound880 (p : Pattern) (guard : walkGuard soko2_2.board support p 211 188 .northWest = true) : bonus 211 p ≤ bonus 188 p := by
  have certified := compare1086 p (guard880 p guard)
  simpa only [at211, at188, Int.zero_add] using certified
theorem check880 (p : Pattern) : (!walkGuard soko2_2.board support p 211 188 .northWest || decide (bonus 211 p ≤ bonus 188 p)) = true :=
  check_of_implication _ _ (bound880 p)
theorem guard881 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 190 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound881 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 190 .north = true) : bonus 212 p ≤ bonus 190 p := by
  have certified := compare1086 p (guard881 p guard)
  simpa only [at212, at190, Int.zero_add] using certified
theorem check881 (p : Pattern) : (!walkGuard soko2_2.board support p 212 190 .north || decide (bonus 212 p ≤ bonus 190 p)) = true :=
  check_of_implication _ _ (bound881 p)
theorem guard882 (p : Pattern) (guard : pushGuard support p 212 190 168 168 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound882 (p : Pattern) (guard : pushGuard support p 212 190 168 168 = true) : bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some 168)) := by
  have certified := compare1087 p (guard882 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 190 (some 168))
  have normalized := agree0 _ _ (change_representative support p 190 (some 168) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check882 (p : Pattern) : (!pushGuard support p 212 190 168 168 || decide (bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some 168)))) = true :=
  check_of_implication _ _ (bound882 p)
theorem guard883 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 213 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound883 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 213 .east = true) : bonus 212 p ≤ bonus 213 p := by
  have certified := compare1086 p (guard883 p guard)
  simpa only [at212, at213, Int.zero_add] using certified
theorem check883 (p : Pattern) : (!walkGuard soko2_2.board support p 212 213 .east || decide (bonus 212 p ≤ bonus 213 p)) = true :=
  check_of_implication _ _ (bound883 p)
theorem guard884 (p : Pattern) (guard : pushGuard support p 212 213 214 214 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound884 (p : Pattern) (guard : pushGuard support p 212 213 214 214 = true) : bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder 214 - Generated.soko2_2Potential.boulder 213 + bonus 213 (change p 213 (some 214)) := by
  have certified := compare1087 p (guard884 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 213 (some 214))
  have normalized := agree0 _ _ (change_representative support p 213 (some 214) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check884 (p : Pattern) : (!pushGuard support p 212 213 214 214 || decide (bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder 214 - Generated.soko2_2Potential.boulder 213 + bonus 213 (change p 213 (some 214)))) = true :=
  check_of_implication _ _ (bound884 p)
theorem guard885 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 211 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound885 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 211 .west = true) : bonus 212 p ≤ bonus 211 p := by
  have certified := compare1086 p (guard885 p guard)
  simpa only [at212, at211, Int.zero_add] using certified
theorem check885 (p : Pattern) : (!walkGuard soko2_2.board support p 212 211 .west || decide (bonus 212 p ≤ bonus 211 p)) = true :=
  check_of_implication _ _ (bound885 p)
theorem guard886 (p : Pattern) (guard : pushGuard support p 212 211 210 210 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound886 (p : Pattern) (guard : pushGuard support p 212 211 210 210 = true) : bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder 210 - Generated.soko2_2Potential.boulder 211 + bonus 211 (change p 211 (some 210)) := by
  have certified := compare1087 p (guard886 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 211 (some 210))
  have normalized := agree0 _ _ (change_representative support p 211 (some 210) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check886 (p : Pattern) : (!pushGuard support p 212 211 210 210 || decide (bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder 210 - Generated.soko2_2Potential.boulder 211 + bonus 211 (change p 211 (some 210)))) = true :=
  check_of_implication _ _ (bound886 p)
theorem guard887 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 191 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound887 (p : Pattern) (guard : walkGuard soko2_2.board support p 212 191 .northEast = true) : bonus 212 p ≤ bonus 191 p := by
  have certified := compare1086 p (guard887 p guard)
  simpa only [at212, at191, Int.zero_add] using certified
theorem check887 (p : Pattern) : (!walkGuard soko2_2.board support p 212 191 .northEast || decide (bonus 212 p ≤ bonus 191 p)) = true :=
  check_of_implication _ _ (bound887 p)
end NetHack.Sokoban22Refined85
