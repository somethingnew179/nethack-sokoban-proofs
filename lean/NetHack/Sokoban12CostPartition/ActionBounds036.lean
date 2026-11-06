import NetHack.Sokoban12CostPartition.ActionBounds035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem guard864 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 332 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound864 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 332 .south = true) : bonus 306 p ≤ bonus 332 p := by
  have certified := compare898 p (guard864 p guard)
  simpa only [at306, at332, Int.zero_add] using certified
theorem check864 (p : Pattern) : (!walkGuard soko1_2.board support p 306 332 .south || decide (bonus 306 p ≤ bonus 332 p)) = true :=
  check_of_implication _ _ (bound864 p)
theorem guard865 (p : Pattern) (guard : pushGuard support p 306 332 358 358 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound865 (p : Pattern) (guard : pushGuard support p 306 332 358 358 = true) : bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some 358)) := by
  have certified := compare1005 p (guard865 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 332 (some 358))
  have normalized := agree0 _ _ (change_representative support p 332 (some 358) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check865 (p : Pattern) : (!pushGuard support p 306 332 358 358 || decide (bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some 358)))) = true :=
  check_of_implication _ _ (bound865 p)
theorem guard866 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 307 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound866 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 307 .east = true) : bonus 306 p ≤ bonus 307 p := by
  have certified := compare898 p (guard866 p guard)
  simpa only [at306, at307, Int.zero_add] using certified
theorem check866 (p : Pattern) : (!walkGuard soko1_2.board support p 306 307 .east || decide (bonus 306 p ≤ bonus 307 p)) = true :=
  check_of_implication _ _ (bound866 p)
theorem guard867 (p : Pattern) (guard : pushGuard support p 306 307 308 308 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound867 (p : Pattern) (guard : pushGuard support p 306 307 308 308 = true) : bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder 308 - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some 308)) := by
  have certified := compare1005 p (guard867 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 307 (some 308))
  have normalized := agree0 _ _ (change_representative support p 307 (some 308) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check867 (p : Pattern) : (!pushGuard support p 306 307 308 308 || decide (bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder 308 - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some 308)))) = true :=
  check_of_implication _ _ (bound867 p)
theorem guard868 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 305 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound868 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 305 .west = true) : bonus 306 p ≤ bonus 305 p := by
  have certified := compare898 p (guard868 p guard)
  simpa only [at306, at305, Int.zero_add] using certified
theorem check868 (p : Pattern) : (!walkGuard soko1_2.board support p 306 305 .west || decide (bonus 306 p ≤ bonus 305 p)) = true :=
  check_of_implication _ _ (bound868 p)
theorem guard869 (p : Pattern) (guard : pushGuard support p 306 305 304 304 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound869 (p : Pattern) (guard : pushGuard support p 306 305 304 304 = true) : bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder 304 - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some 304)) := by
  have certified := compare1005 p (guard869 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 305 (some 304))
  have normalized := agree0 _ _ (change_representative support p 305 (some 304) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check869 (p : Pattern) : (!pushGuard support p 306 305 304 304 || decide (bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder 304 - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some 304)))) = true :=
  check_of_implication _ _ (bound869 p)
theorem guard870 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 281 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound870 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 281 .northEast = true) : bonus 306 p ≤ bonus 281 p := by
  have certified := compare898 p (guard870 p guard)
  simpa only [at306, at281, Int.zero_add] using certified
theorem check870 (p : Pattern) : (!walkGuard soko1_2.board support p 306 281 .northEast || decide (bonus 306 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound870 p)
theorem guard871 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 279 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound871 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 279 .northWest = true) : bonus 306 p ≤ bonus 279 p := by
  have certified := compare898 p (guard871 p guard)
  simpa only [at306, at279, Int.zero_add] using certified
theorem check871 (p : Pattern) : (!walkGuard soko1_2.board support p 306 279 .northWest || decide (bonus 306 p ≤ bonus 279 p)) = true :=
  check_of_implication _ _ (bound871 p)
theorem guard872 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 333 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound872 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 333 .southEast = true) : bonus 306 p ≤ bonus 333 p := by
  have certified := compare898 p (guard872 p guard)
  simpa only [at306, at333, Int.zero_add] using certified
theorem check872 (p : Pattern) : (!walkGuard soko1_2.board support p 306 333 .southEast || decide (bonus 306 p ≤ bonus 333 p)) = true :=
  check_of_implication _ _ (bound872 p)
theorem guard873 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 331 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound873 (p : Pattern) (guard : walkGuard soko1_2.board support p 306 331 .southWest = true) : bonus 306 p ≤ bonus 331 p := by
  have certified := compare898 p (guard873 p guard)
  simpa only [at306, at331, Int.zero_add] using certified
theorem check873 (p : Pattern) : (!walkGuard soko1_2.board support p 306 331 .southWest || decide (bonus 306 p ≤ bonus 331 p)) = true :=
  check_of_implication _ _ (bound873 p)
theorem guard874 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 281 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound874 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 281 .north = true) : bonus 307 p ≤ bonus 281 p := by
  have certified := compare898 p (guard874 p guard)
  simpa only [at307, at281, Int.zero_add] using certified
theorem check874 (p : Pattern) : (!walkGuard soko1_2.board support p 307 281 .north || decide (bonus 307 p ≤ bonus 281 p)) = true :=
  check_of_implication _ _ (bound874 p)
theorem guard875 (p : Pattern) (guard : pushGuard support p 307 281 255 255 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound875 (p : Pattern) (guard : pushGuard support p 307 281 255 255 = true) : bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder 255 - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some 255)) := by
  have certified := compare1005 p (guard875 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 281 (some 255))
  have normalized := agree0 _ _ (change_representative support p 281 (some 255) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check875 (p : Pattern) : (!pushGuard support p 307 281 255 255 || decide (bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder 255 - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some 255)))) = true :=
  check_of_implication _ _ (bound875 p)
theorem guard876 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 333 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound876 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 333 .south = true) : bonus 307 p ≤ bonus 333 p := by
  have certified := compare898 p (guard876 p guard)
  simpa only [at307, at333, Int.zero_add] using certified
theorem check876 (p : Pattern) : (!walkGuard soko1_2.board support p 307 333 .south || decide (bonus 307 p ≤ bonus 333 p)) = true :=
  check_of_implication _ _ (bound876 p)
theorem guard877 (p : Pattern) (guard : pushGuard support p 307 333 359 359 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound877 (p : Pattern) (guard : pushGuard support p 307 333 359 359 = true) : bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some 359)) := by
  have certified := compare1005 p (guard877 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 333 (some 359))
  have normalized := agree0 _ _ (change_representative support p 333 (some 359) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check877 (p : Pattern) : (!pushGuard support p 307 333 359 359 || decide (bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some 359)))) = true :=
  check_of_implication _ _ (bound877 p)
theorem guard878 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 308 .east = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound878 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 308 .east = true) : bonus 307 p ≤ bonus 308 p := by
  have certified := compare898 p (guard878 p guard)
  simpa only [at307, at308, Int.zero_add] using certified
theorem check878 (p : Pattern) : (!walkGuard soko1_2.board support p 307 308 .east || decide (bonus 307 p ≤ bonus 308 p)) = true :=
  check_of_implication _ _ (bound878 p)
theorem guard879 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 306 .west = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound879 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 306 .west = true) : bonus 307 p ≤ bonus 306 p := by
  have certified := compare898 p (guard879 p guard)
  simpa only [at307, at306, Int.zero_add] using certified
theorem check879 (p : Pattern) : (!walkGuard soko1_2.board support p 307 306 .west || decide (bonus 307 p ≤ bonus 306 p)) = true :=
  check_of_implication _ _ (bound879 p)
theorem guard880 (p : Pattern) (guard : pushGuard support p 307 306 305 305 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound880 (p : Pattern) (guard : pushGuard support p 307 306 305 305 = true) : bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some 305)) := by
  have certified := compare1005 p (guard880 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 306 (some 305))
  have normalized := agree0 _ _ (change_representative support p 306 (some 305) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check880 (p : Pattern) : (!pushGuard support p 307 306 305 305 || decide (bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some 305)))) = true :=
  check_of_implication _ _ (bound880 p)
theorem guard881 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 282 .northEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound881 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 282 .northEast = true) : bonus 307 p ≤ bonus 282 p := by
  have certified := compare898 p (guard881 p guard)
  simpa only [at307, at282, Int.zero_add] using certified
theorem check881 (p : Pattern) : (!walkGuard soko1_2.board support p 307 282 .northEast || decide (bonus 307 p ≤ bonus 282 p)) = true :=
  check_of_implication _ _ (bound881 p)
theorem guard882 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 280 .northWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound882 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 280 .northWest = true) : bonus 307 p ≤ bonus 280 p := by
  have certified := compare898 p (guard882 p guard)
  simpa only [at307, at280, Int.zero_add] using certified
theorem check882 (p : Pattern) : (!walkGuard soko1_2.board support p 307 280 .northWest || decide (bonus 307 p ≤ bonus 280 p)) = true :=
  check_of_implication _ _ (bound882 p)
theorem guard883 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 334 .southEast = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound883 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 334 .southEast = true) : bonus 307 p ≤ bonus 334 p := by
  have certified := compare898 p (guard883 p guard)
  simpa only [at307, at334, Int.zero_add] using certified
theorem check883 (p : Pattern) : (!walkGuard soko1_2.board support p 307 334 .southEast || decide (bonus 307 p ≤ bonus 334 p)) = true :=
  check_of_implication _ _ (bound883 p)
theorem guard884 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 332 .southWest = true) : d1 p = 1 := by
  change (!false && !false && !(true && false && false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound884 (p : Pattern) (guard : walkGuard soko1_2.board support p 307 332 .southWest = true) : bonus 307 p ≤ bonus 332 p := by
  have certified := compare898 p (guard884 p guard)
  simpa only [at307, at332, Int.zero_add] using certified
theorem check884 (p : Pattern) : (!walkGuard soko1_2.board support p 307 332 .southWest || decide (bonus 307 p ≤ bonus 332 p)) = true :=
  check_of_implication _ _ (bound884 p)
theorem guard885 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 282 .north = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound885 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 282 .north = true) : bonus 308 p ≤ bonus 282 p := by
  have certified := compare898 p (guard885 p guard)
  simpa only [at308, at282, Int.zero_add] using certified
theorem check885 (p : Pattern) : (!walkGuard soko1_2.board support p 308 282 .north || decide (bonus 308 p ≤ bonus 282 p)) = true :=
  check_of_implication _ _ (bound885 p)
theorem guard886 (p : Pattern) (guard : pushGuard support p 308 282 256 256 = true) : d1 p = 1 := by
  change (!false && (!false || false) && !false && (!false || false)) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound886 (p : Pattern) (guard : pushGuard support p 308 282 256 256 = true) : bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder 256 - Generated.soko1_2Potential.boulder 282 + bonus 282 (change p 282 (some 256)) := by
  have certified := compare1005 p (guard886 p guard)
  change d0 p ≤ (1 : Int) + d0 (change p 282 (some 256))
  have normalized := agree0 _ _ (change_representative support p 282 (some 256) 10000 dummy_outside)
  rw [normalized]
  change d0 p ≤ (1 : Int) + d0 (change p 10000 none)
  rw [sub0]
  exact certified
theorem check886 (p : Pattern) : (!pushGuard support p 308 282 256 256 || decide (bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder 256 - Generated.soko1_2Potential.boulder 282 + bonus 282 (change p 282 (some 256)))) = true :=
  check_of_implication _ _ (bound886 p)
theorem guard887 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 334 .south = true) : d1 p = 1 := by
  change (!false && !false && !false) = true at guard
  all_goals simp [d1] at guard ⊢
theorem bound887 (p : Pattern) (guard : walkGuard soko1_2.board support p 308 334 .south = true) : bonus 308 p ≤ bonus 334 p := by
  have certified := compare898 p (guard887 p guard)
  simpa only [at308, at334, Int.zero_add] using certified
theorem check887 (p : Pattern) : (!walkGuard soko1_2.board support p 308 334 .south || decide (bonus 308 p ≤ bonus 334 p)) = true :=
  check_of_implication _ _ (bound887 p)
end NetHack.Sokoban12CostPartition
