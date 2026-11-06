import NetHack.Sokoban22Refined85.Directions16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir199_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 .north p = true := by
  change ((!walkGuard soko2_2.board support p 199 177 .north || decide (bonus 199 p ≤ bonus 177 p)) && ((PreciseRolling.stayTargets soko2_2.board 177 .north).all (fun landing => !pushGuard support p 199 177 155 landing || decide (bonus 199 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 177 + bonus 177 (change p 177 (some landing)))) && (pushTargets soko2_2.board 177 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 199 177 155 landing || decide (bonus 199 p ≤ 1 - Generated.soko2_2Potential.boulder 177 - Generated.soko2_2Potential.hole landing + bonus 177 (change p 177 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check838 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check839 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir199_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 .south p = true := by
  rfl
theorem dir199_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 .east p = true := by
  change ((!walkGuard soko2_2.board support p 199 200 .east || decide (bonus 199 p ≤ bonus 200 p)) && ((PreciseRolling.stayTargets soko2_2.board 200 .east).all (fun landing => !pushGuard support p 199 200 201 landing || decide (bonus 199 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 200 + bonus 200 (change p 200 (some landing)))) && (pushTargets soko2_2.board 200 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 199 200 201 landing || decide (bonus 199 p ≤ 1 - Generated.soko2_2Potential.boulder 200 - Generated.soko2_2Potential.hole landing + bonus 200 (change p 200 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check840 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check841 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir199_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 .west p = true := by
  rfl
theorem dir199_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 .northEast p = true := by
  rfl
theorem dir199_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 .northWest p = true := by
  rfl
theorem dir199_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 .southEast p = true := by
  rfl
theorem dir199_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 199 .southWest p = true := by
  rfl
theorem dir200_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 .north p = true := by
  rfl
theorem dir200_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 .south p = true := by
  rfl
theorem dir200_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 .east p = true := by
  change ((!walkGuard soko2_2.board support p 200 201 .east || decide (bonus 200 p ≤ bonus 201 p)) && ((PreciseRolling.stayTargets soko2_2.board 201 .east).all (fun landing => !pushGuard support p 200 201 202 landing || decide (bonus 200 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 201 + bonus 201 (change p 201 (some landing)))) && (pushTargets soko2_2.board 201 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 200 201 202 landing || decide (bonus 200 p ≤ 1 - Generated.soko2_2Potential.boulder 201 - Generated.soko2_2Potential.hole landing + bonus 201 (change p 201 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check842 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check843 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir200_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 .west p = true := by
  change ((!walkGuard soko2_2.board support p 200 199 .west || decide (bonus 200 p ≤ bonus 199 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check844 p, rfl⟩
theorem dir200_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 .northEast p = true := by
  rfl
theorem dir200_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 200 177 .northWest || decide (bonus 200 p ≤ bonus 177 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check845 p, rfl⟩
theorem dir200_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 200 223 .southEast || decide (bonus 200 p ≤ bonus 223 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check846 p, rfl⟩
theorem dir200_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 200 .southWest p = true := by
  rfl
theorem dir201_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 .north p = true := by
  rfl
theorem dir201_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 .south p = true := by
  change ((!walkGuard soko2_2.board support p 201 223 .south || decide (bonus 201 p ≤ bonus 223 p)) && ((PreciseRolling.stayTargets soko2_2.board 223 .south).all (fun landing => !pushGuard support p 201 223 245 landing || decide (bonus 201 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 223 + bonus 223 (change p 223 (some landing)))) && (pushTargets soko2_2.board 223 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 201 223 245 landing || decide (bonus 201 p ≤ 1 - Generated.soko2_2Potential.boulder 223 - Generated.soko2_2Potential.hole landing + bonus 223 (change p 223 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check847 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check848 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir201_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 .east p = true := by
  change ((!walkGuard soko2_2.board support p 201 202 .east || decide (bonus 201 p ≤ bonus 202 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check849 p, rfl⟩
theorem dir201_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 .west p = true := by
  change ((!walkGuard soko2_2.board support p 201 200 .west || decide (bonus 201 p ≤ bonus 200 p)) && ((PreciseRolling.stayTargets soko2_2.board 200 .west).all (fun landing => !pushGuard support p 201 200 199 landing || decide (bonus 201 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 200 + bonus 200 (change p 200 (some landing)))) && (pushTargets soko2_2.board 200 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 201 200 199 landing || decide (bonus 201 p ≤ 1 - Generated.soko2_2Potential.boulder 200 - Generated.soko2_2Potential.hole landing + bonus 200 (change p 200 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check850 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check851 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir201_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 201 180 .northEast || decide (bonus 201 p ≤ bonus 180 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check852 p, rfl⟩
theorem dir201_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 .northWest p = true := by
  rfl
theorem dir201_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 201 224 .southEast || decide (bonus 201 p ≤ bonus 224 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check853 p, rfl⟩
theorem dir201_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 201 .southWest p = true := by
  rfl
theorem dir202_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 .north p = true := by
  change ((!walkGuard soko2_2.board support p 202 180 .north || decide (bonus 202 p ≤ bonus 180 p)) && ((PreciseRolling.stayTargets soko2_2.board 180 .north).all (fun landing => !pushGuard support p 202 180 158 landing || decide (bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 180 + bonus 180 (change p 180 (some landing)))) && (pushTargets soko2_2.board 180 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 202 180 158 landing || decide (bonus 202 p ≤ 1 - Generated.soko2_2Potential.boulder 180 - Generated.soko2_2Potential.hole landing + bonus 180 (change p 180 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check854 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check855 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir202_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 .south p = true := by
  change ((!walkGuard soko2_2.board support p 202 224 .south || decide (bonus 202 p ≤ bonus 224 p)) && ((PreciseRolling.stayTargets soko2_2.board 224 .south).all (fun landing => !pushGuard support p 202 224 246 landing || decide (bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some landing)))) && (pushTargets soko2_2.board 224 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 202 224 246 landing || decide (bonus 202 p ≤ 1 - Generated.soko2_2Potential.boulder 224 - Generated.soko2_2Potential.hole landing + bonus 224 (change p 224 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check856 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check857 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir202_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 .east p = true := by
  rfl
theorem dir202_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 .west p = true := by
  change ((!walkGuard soko2_2.board support p 202 201 .west || decide (bonus 202 p ≤ bonus 201 p)) && ((PreciseRolling.stayTargets soko2_2.board 201 .west).all (fun landing => !pushGuard support p 202 201 200 landing || decide (bonus 202 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 201 + bonus 201 (change p 201 (some landing)))) && (pushTargets soko2_2.board 201 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 202 201 200 landing || decide (bonus 202 p ≤ 1 - Generated.soko2_2Potential.boulder 201 - Generated.soko2_2Potential.hole landing + bonus 201 (change p 201 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check858 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check859 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir202_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 202 181 .northEast || decide (bonus 202 p ≤ bonus 181 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check860 p, rfl⟩
theorem dir202_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 .northWest p = true := by
  rfl
theorem dir202_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 202 225 .southEast || decide (bonus 202 p ≤ bonus 225 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check861 p, rfl⟩
theorem dir202_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 202 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 202 223 .southWest || decide (bonus 202 p ≤ bonus 223 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check862 p, rfl⟩
theorem dir204_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 .north p = true := by
  change ((!walkGuard soko2_2.board support p 204 182 .north || decide (bonus 204 p ≤ bonus 182 p)) && ((PreciseRolling.stayTargets soko2_2.board 182 .north).all (fun landing => !pushGuard support p 204 182 160 landing || decide (bonus 204 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 182 + bonus 182 (change p 182 (some landing)))) && (pushTargets soko2_2.board 182 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 204 182 160 landing || decide (bonus 204 p ≤ 1 - Generated.soko2_2Potential.boulder 182 - Generated.soko2_2Potential.hole landing + bonus 182 (change p 182 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check863 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check864 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir204_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 .south p = true := by
  change ((!walkGuard soko2_2.board support p 204 226 .south || decide (bonus 204 p ≤ bonus 226 p)) && ((PreciseRolling.stayTargets soko2_2.board 226 .south).all (fun landing => !pushGuard support p 204 226 248 landing || decide (bonus 204 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 226 + bonus 226 (change p 226 (some landing)))) && (pushTargets soko2_2.board 226 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 204 226 248 landing || decide (bonus 204 p ≤ 1 - Generated.soko2_2Potential.boulder 226 - Generated.soko2_2Potential.hole landing + bonus 226 (change p 226 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check865 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check866 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir204_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 .east p = true := by
  rfl
theorem dir204_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 .west p = true := by
  rfl
theorem dir204_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 .northEast p = true := by
  rfl
theorem dir204_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 204 181 .northWest || decide (bonus 204 p ≤ bonus 181 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check867 p, rfl⟩
theorem dir204_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 .southEast p = true := by
  rfl
theorem dir204_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 204 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 204 225 .southWest || decide (bonus 204 p ≤ bonus 225 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check868 p, rfl⟩
theorem dir210_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 .north p = true := by
  change ((!walkGuard soko2_2.board support p 210 188 .north || decide (bonus 210 p ≤ bonus 188 p)) && ((PreciseRolling.stayTargets soko2_2.board 188 .north).all (fun landing => !pushGuard support p 210 188 166 landing || decide (bonus 210 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 188 + bonus 188 (change p 188 (some landing)))) && (pushTargets soko2_2.board 188 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 210 188 166 landing || decide (bonus 210 p ≤ 1 - Generated.soko2_2Potential.boulder 188 - Generated.soko2_2Potential.hole landing + bonus 188 (change p 188 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check869 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check870 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir210_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 .south p = true := by
  rfl
theorem dir210_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 .east p = true := by
  change ((!walkGuard soko2_2.board support p 210 211 .east || decide (bonus 210 p ≤ bonus 211 p)) && ((PreciseRolling.stayTargets soko2_2.board 211 .east).all (fun landing => !pushGuard support p 210 211 212 landing || decide (bonus 210 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 211 + bonus 211 (change p 211 (some landing)))) && (pushTargets soko2_2.board 211 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 210 211 212 landing || decide (bonus 210 p ≤ 1 - Generated.soko2_2Potential.boulder 211 - Generated.soko2_2Potential.hole landing + bonus 211 (change p 211 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check871 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check872 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir210_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 .west p = true := by
  rfl
theorem dir210_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 210 189 .northEast || decide (bonus 210 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check873 p, rfl⟩
theorem dir210_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 .northWest p = true := by
  rfl
theorem dir210_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 .southEast p = true := by
  rfl
theorem dir210_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 210 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
