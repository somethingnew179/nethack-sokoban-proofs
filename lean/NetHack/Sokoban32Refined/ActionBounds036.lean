import NetHack.Sokoban32Refined.ActionBounds035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard864 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 225 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound864 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 225 .south = true) : bonus 199 p ≤ bonus 225 p := by
  have certified := compare103 p (guard864 p guard)
  simpa only [at199, at225, Int.zero_add] using certified
theorem check864 (p : Pattern) : (!walkGuard soko3_2.board support p 199 225 .south || decide (bonus 199 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound864 p)
theorem guard865 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 200 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound865 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 200 .east = true) : bonus 199 p ≤ bonus 200 p := by
  have certified := compare103 p (guard865 p guard)
  simpa only [at199, at200, Int.zero_add] using certified
theorem check865 (p : Pattern) : (!walkGuard soko3_2.board support p 199 200 .east || decide (bonus 199 p ≤ bonus 200 p)) = true :=
  check_of_implication _ _ (bound865 p)
theorem guard866 (p : Pattern) (guard : pushGuard support p 199 200 201 201 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound866 (p : Pattern) (guard : pushGuard support p 199 200 201 201 = true) : bonus 199 p ≤ 1 + Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some 201)) := by
  have certified := compare37 p (guard866 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 200 (some 201))
  have normalized := agree0 _ _ (change_representative support p 200 (some 201) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check866 (p : Pattern) : (!pushGuard support p 199 200 201 201 || decide (bonus 199 p ≤ 1 + Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some 201)))) = true :=
  check_of_implication _ _ (bound866 p)
theorem guard867 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 198 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound867 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 198 .west = true) : bonus 199 p ≤ bonus 198 p := by
  have certified := compare103 p (guard867 p guard)
  simpa only [at199, at198, Int.zero_add] using certified
theorem check867 (p : Pattern) : (!walkGuard soko3_2.board support p 199 198 .west || decide (bonus 199 p ≤ bonus 198 p)) = true :=
  check_of_implication _ _ (bound867 p)
theorem guard868 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 174 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound868 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 174 .northEast = true) : bonus 199 p ≤ bonus 174 p := by
  have certified := compare103 p (guard868 p guard)
  simpa only [at199, at174, Int.zero_add] using certified
theorem check868 (p : Pattern) : (!walkGuard soko3_2.board support p 199 174 .northEast || decide (bonus 199 p ≤ bonus 174 p)) = true :=
  check_of_implication _ _ (bound868 p)
theorem guard869 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 172 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound869 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 172 .northWest = true) : bonus 199 p ≤ bonus 172 p := by
  have certified := compare103 p (guard869 p guard)
  simpa only [at199, at172, Int.zero_add] using certified
theorem check869 (p : Pattern) : (!walkGuard soko3_2.board support p 199 172 .northWest || decide (bonus 199 p ≤ bonus 172 p)) = true :=
  check_of_implication _ _ (bound869 p)
theorem guard870 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 226 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound870 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 226 .southEast = true) : bonus 199 p ≤ bonus 226 p := by
  have certified := compare103 p (guard870 p guard)
  simpa only [at199, at226, Int.zero_add] using certified
theorem check870 (p : Pattern) : (!walkGuard soko3_2.board support p 199 226 .southEast || decide (bonus 199 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound870 p)
theorem guard871 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 224 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound871 (p : Pattern) (guard : walkGuard soko3_2.board support p 199 224 .southWest = true) : bonus 199 p ≤ bonus 224 p := by
  have certified := compare103 p (guard871 p guard)
  simpa only [at199, at224, Int.zero_add] using certified
theorem check871 (p : Pattern) : (!walkGuard soko3_2.board support p 199 224 .southWest || decide (bonus 199 p ≤ bonus 224 p)) = true :=
  check_of_implication _ _ (bound871 p)
theorem guard872 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 174 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound872 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 174 .north = true) : bonus 200 p ≤ bonus 174 p := by
  have certified := compare103 p (guard872 p guard)
  simpa only [at200, at174, Int.zero_add] using certified
theorem check872 (p : Pattern) : (!walkGuard soko3_2.board support p 200 174 .north || decide (bonus 200 p ≤ bonus 174 p)) = true :=
  check_of_implication _ _ (bound872 p)
theorem guard873 (p : Pattern) (guard : pushGuard support p 200 174 148 148 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound873 (p : Pattern) (guard : pushGuard support p 200 174 148 148 = true) : bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some 148)) := by
  have certified := compare37 p (guard873 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 174 (some 148))
  have normalized := agree0 _ _ (change_representative support p 174 (some 148) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check873 (p : Pattern) : (!pushGuard support p 200 174 148 148 || decide (bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some 148)))) = true :=
  check_of_implication _ _ (bound873 p)
theorem guard874 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 226 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound874 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 226 .south = true) : bonus 200 p ≤ bonus 226 p := by
  have certified := compare103 p (guard874 p guard)
  simpa only [at200, at226, Int.zero_add] using certified
theorem check874 (p : Pattern) : (!walkGuard soko3_2.board support p 200 226 .south || decide (bonus 200 p ≤ bonus 226 p)) = true :=
  check_of_implication _ _ (bound874 p)
theorem guard875 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 201 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound875 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 201 .east = true) : bonus 200 p ≤ bonus 201 p := by
  have certified := compare103 p (guard875 p guard)
  simpa only [at200, at201, Int.zero_add] using certified
theorem check875 (p : Pattern) : (!walkGuard soko3_2.board support p 200 201 .east || decide (bonus 200 p ≤ bonus 201 p)) = true :=
  check_of_implication _ _ (bound875 p)
theorem guard876 (p : Pattern) (guard : pushGuard support p 200 201 202 202 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound876 (p : Pattern) (guard : pushGuard support p 200 201 202 202 = true) : bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some 202)) := by
  have certified := compare37 p (guard876 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 201 (some 202))
  have normalized := agree0 _ _ (change_representative support p 201 (some 202) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check876 (p : Pattern) : (!pushGuard support p 200 201 202 202 || decide (bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some 202)))) = true :=
  check_of_implication _ _ (bound876 p)
theorem guard877 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 199 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound877 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 199 .west = true) : bonus 200 p ≤ bonus 199 p := by
  have certified := compare103 p (guard877 p guard)
  simpa only [at200, at199, Int.zero_add] using certified
theorem check877 (p : Pattern) : (!walkGuard soko3_2.board support p 200 199 .west || decide (bonus 200 p ≤ bonus 199 p)) = true :=
  check_of_implication _ _ (bound877 p)
theorem guard878 (p : Pattern) (guard : pushGuard support p 200 199 198 198 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound878 (p : Pattern) (guard : pushGuard support p 200 199 198 198 = true) : bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder 198 - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some 198)) := by
  have certified := compare37 p (guard878 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 199 (some 198))
  have normalized := agree0 _ _ (change_representative support p 199 (some 198) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check878 (p : Pattern) : (!pushGuard support p 200 199 198 198 || decide (bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder 198 - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some 198)))) = true :=
  check_of_implication _ _ (bound878 p)
theorem guard879 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 175 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound879 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 175 .northEast = true) : bonus 200 p ≤ bonus 175 p := by
  have certified := compare103 p (guard879 p guard)
  simpa only [at200, at175, Int.zero_add] using certified
theorem check879 (p : Pattern) : (!walkGuard soko3_2.board support p 200 175 .northEast || decide (bonus 200 p ≤ bonus 175 p)) = true :=
  check_of_implication _ _ (bound879 p)
theorem guard880 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 173 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound880 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 173 .northWest = true) : bonus 200 p ≤ bonus 173 p := by
  have certified := compare103 p (guard880 p guard)
  simpa only [at200, at173, Int.zero_add] using certified
theorem check880 (p : Pattern) : (!walkGuard soko3_2.board support p 200 173 .northWest || decide (bonus 200 p ≤ bonus 173 p)) = true :=
  check_of_implication _ _ (bound880 p)
theorem guard881 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 227 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound881 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 227 .southEast = true) : bonus 200 p ≤ bonus 227 p := by
  have certified := compare103 p (guard881 p guard)
  simpa only [at200, at227, Int.zero_add] using certified
theorem check881 (p : Pattern) : (!walkGuard soko3_2.board support p 200 227 .southEast || decide (bonus 200 p ≤ bonus 227 p)) = true :=
  check_of_implication _ _ (bound881 p)
theorem guard882 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 225 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound882 (p : Pattern) (guard : walkGuard soko3_2.board support p 200 225 .southWest = true) : bonus 200 p ≤ bonus 225 p := by
  have certified := compare103 p (guard882 p guard)
  simpa only [at200, at225, Int.zero_add] using certified
theorem check882 (p : Pattern) : (!walkGuard soko3_2.board support p 200 225 .southWest || decide (bonus 200 p ≤ bonus 225 p)) = true :=
  check_of_implication _ _ (bound882 p)
theorem guard883 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 175 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound883 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 175 .north = true) : bonus 201 p ≤ bonus 175 p := by
  have certified := compare103 p (guard883 p guard)
  simpa only [at201, at175, Int.zero_add] using certified
theorem check883 (p : Pattern) : (!walkGuard soko3_2.board support p 201 175 .north || decide (bonus 201 p ≤ bonus 175 p)) = true :=
  check_of_implication _ _ (bound883 p)
theorem guard884 (p : Pattern) (guard : pushGuard support p 201 175 149 149 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound884 (p : Pattern) (guard : pushGuard support p 201 175 149 149 = true) : bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some 149)) := by
  have certified := compare37 p (guard884 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 175 (some 149))
  have normalized := agree0 _ _ (change_representative support p 175 (some 149) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check884 (p : Pattern) : (!pushGuard support p 201 175 149 149 || decide (bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some 149)))) = true :=
  check_of_implication _ _ (bound884 p)
theorem guard885 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 227 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound885 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 227 .south = true) : bonus 201 p ≤ bonus 227 p := by
  have certified := compare103 p (guard885 p guard)
  simpa only [at201, at227, Int.zero_add] using certified
theorem check885 (p : Pattern) : (!walkGuard soko3_2.board support p 201 227 .south || decide (bonus 201 p ≤ bonus 227 p)) = true :=
  check_of_implication _ _ (bound885 p)
theorem guard886 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 202 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound886 (p : Pattern) (guard : walkGuard soko3_2.board support p 201 202 .east = true) : bonus 201 p ≤ bonus 202 p := by
  have certified := compare103 p (guard886 p guard)
  simpa only [at201, at202, Int.zero_add] using certified
theorem check886 (p : Pattern) : (!walkGuard soko3_2.board support p 201 202 .east || decide (bonus 201 p ≤ bonus 202 p)) = true :=
  check_of_implication _ _ (bound886 p)
theorem guard887 (p : Pattern) (guard : pushGuard support p 201 202 203 203 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound887 (p : Pattern) (guard : pushGuard support p 201 202 203 203 = true) : bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some 203)) := by
  have certified := compare37 p (guard887 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 202 (some 203))
  have normalized := agree0 _ _ (change_representative support p 202 (some 203) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub115]
  exact certified
theorem check887 (p : Pattern) : (!pushGuard support p 201 202 203 203 || decide (bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some 203)))) = true :=
  check_of_implication _ _ (bound887 p)
end NetHack.Sokoban32Refined
