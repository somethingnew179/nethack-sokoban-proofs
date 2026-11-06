import NetHack.Sokoban22Refined85.ActionBounds044
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir25_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 .north p = true := by
  rfl
theorem dir25_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 .south p = true := by
  change ((!walkGuard soko2_2.board support p 25 47 .south || decide (bonus 25 p ≤ bonus 47 p)) && ((PreciseRolling.stayTargets soko2_2.board 47 .south).all (fun landing => !pushGuard support p 25 47 69 landing || decide (bonus 25 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some landing)))) && (pushTargets soko2_2.board 47 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 25 47 69 landing || decide (bonus 25 p ≤ 1 - Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.hole landing + bonus 47 (change p 47 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check0 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir25_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 .east p = true := by
  rfl
theorem dir25_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 .west p = true := by
  rfl
theorem dir25_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 .northEast p = true := by
  rfl
theorem dir25_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 .northWest p = true := by
  rfl
theorem dir25_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 25 48 .southEast || decide (bonus 25 p ≤ bonus 48 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check2 p, rfl⟩
theorem dir25_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 25 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 25 46 .southWest || decide (bonus 25 p ≤ bonus 46 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check3 p, rfl⟩
theorem dir27_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 .north p = true := by
  rfl
theorem dir27_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 .south p = true := by
  change ((!walkGuard soko2_2.board support p 27 49 .south || decide (bonus 27 p ≤ bonus 49 p)) && ((PreciseRolling.stayTargets soko2_2.board 49 .south).all (fun landing => !pushGuard support p 27 49 71 landing || decide (bonus 27 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some landing)))) && (pushTargets soko2_2.board 49 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 27 49 71 landing || decide (bonus 27 p ≤ 1 - Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.hole landing + bonus 49 (change p 49 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check4 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check5 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir27_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 .east p = true := by
  change ((!walkGuard soko2_2.board support p 27 28 .east || decide (bonus 27 p ≤ bonus 28 p)) && ((PreciseRolling.stayTargets soko2_2.board 28 .east).all (fun landing => !pushGuard support p 27 28 29 landing || decide (bonus 27 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 28 + bonus 28 (change p 28 (some landing)))) && (pushTargets soko2_2.board 28 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 27 28 29 landing || decide (bonus 27 p ≤ 1 - Generated.soko2_2Potential.boulder 28 - Generated.soko2_2Potential.hole landing + bonus 28 (change p 28 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check6 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check7 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir27_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 .west p = true := by
  rfl
theorem dir27_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 .northEast p = true := by
  rfl
theorem dir27_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 .northWest p = true := by
  rfl
theorem dir27_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 27 50 .southEast || decide (bonus 27 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check8 p, rfl⟩
theorem dir27_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 27 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 27 48 .southWest || decide (bonus 27 p ≤ bonus 48 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check9 p, rfl⟩
theorem dir28_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 .north p = true := by
  rfl
theorem dir28_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 .south p = true := by
  change ((!walkGuard soko2_2.board support p 28 50 .south || decide (bonus 28 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check10 p, rfl⟩
theorem dir28_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 .east p = true := by
  change ((!walkGuard soko2_2.board support p 28 29 .east || decide (bonus 28 p ≤ bonus 29 p)) && ((PreciseRolling.stayTargets soko2_2.board 29 .east).all (fun landing => !pushGuard support p 28 29 30 landing || decide (bonus 28 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 29 + bonus 29 (change p 29 (some landing)))) && (pushTargets soko2_2.board 29 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 28 29 30 landing || decide (bonus 28 p ≤ 1 - Generated.soko2_2Potential.boulder 29 - Generated.soko2_2Potential.hole landing + bonus 29 (change p 29 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check11 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check12 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir28_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 .west p = true := by
  change ((!walkGuard soko2_2.board support p 28 27 .west || decide (bonus 28 p ≤ bonus 27 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check13 p, rfl⟩
theorem dir28_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 .northEast p = true := by
  rfl
theorem dir28_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 .northWest p = true := by
  rfl
theorem dir28_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 28 51 .southEast || decide (bonus 28 p ≤ bonus 51 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check14 p, rfl⟩
theorem dir28_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 28 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 28 49 .southWest || decide (bonus 28 p ≤ bonus 49 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check15 p, rfl⟩
theorem dir29_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 .north p = true := by
  rfl
theorem dir29_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 .south p = true := by
  change ((!walkGuard soko2_2.board support p 29 51 .south || decide (bonus 29 p ≤ bonus 51 p)) && ((PreciseRolling.stayTargets soko2_2.board 51 .south).all (fun landing => !pushGuard support p 29 51 73 landing || decide (bonus 29 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some landing)))) && (pushTargets soko2_2.board 51 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 29 51 73 landing || decide (bonus 29 p ≤ 1 - Generated.soko2_2Potential.boulder 51 - Generated.soko2_2Potential.hole landing + bonus 51 (change p 51 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check16 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check17 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir29_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 .east p = true := by
  change ((!walkGuard soko2_2.board support p 29 30 .east || decide (bonus 29 p ≤ bonus 30 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check18 p, rfl⟩
theorem dir29_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 .west p = true := by
  change ((!walkGuard soko2_2.board support p 29 28 .west || decide (bonus 29 p ≤ bonus 28 p)) && ((PreciseRolling.stayTargets soko2_2.board 28 .west).all (fun landing => !pushGuard support p 29 28 27 landing || decide (bonus 29 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 28 + bonus 28 (change p 28 (some landing)))) && (pushTargets soko2_2.board 28 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 29 28 27 landing || decide (bonus 29 p ≤ 1 - Generated.soko2_2Potential.boulder 28 - Generated.soko2_2Potential.hole landing + bonus 28 (change p 28 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check19 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check20 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir29_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 .northEast p = true := by
  rfl
theorem dir29_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 .northWest p = true := by
  rfl
theorem dir29_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 29 52 .southEast || decide (bonus 29 p ≤ bonus 52 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check21 p, rfl⟩
theorem dir29_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 29 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 29 50 .southWest || decide (bonus 29 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check22 p, rfl⟩
theorem dir30_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 .north p = true := by
  rfl
theorem dir30_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 .south p = true := by
  change ((!walkGuard soko2_2.board support p 30 52 .south || decide (bonus 30 p ≤ bonus 52 p)) && ((PreciseRolling.stayTargets soko2_2.board 52 .south).all (fun landing => !pushGuard support p 30 52 74 landing || decide (bonus 30 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 52 + bonus 52 (change p 52 (some landing)))) && (pushTargets soko2_2.board 52 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 30 52 74 landing || decide (bonus 30 p ≤ 1 - Generated.soko2_2Potential.boulder 52 - Generated.soko2_2Potential.hole landing + bonus 52 (change p 52 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check23 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check24 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir30_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 .east p = true := by
  rfl
theorem dir30_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 .west p = true := by
  change ((!walkGuard soko2_2.board support p 30 29 .west || decide (bonus 30 p ≤ bonus 29 p)) && ((PreciseRolling.stayTargets soko2_2.board 29 .west).all (fun landing => !pushGuard support p 30 29 28 landing || decide (bonus 30 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 29 + bonus 29 (change p 29 (some landing)))) && (pushTargets soko2_2.board 29 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 30 29 28 landing || decide (bonus 30 p ≤ 1 - Generated.soko2_2Potential.boulder 29 - Generated.soko2_2Potential.hole landing + bonus 29 (change p 29 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check25 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check26 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir30_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 .northEast p = true := by
  rfl
theorem dir30_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 .northWest p = true := by
  rfl
theorem dir30_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 .southEast p = true := by
  rfl
theorem dir30_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 30 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 30 51 .southWest || decide (bonus 30 p ≤ bonus 51 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check27 p, rfl⟩
theorem dir45_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 .north p = true := by
  rfl
theorem dir45_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 .south p = true := by
  change ((!walkGuard soko2_2.board support p 45 67 .south || decide (bonus 45 p ≤ bonus 67 p)) && ((PreciseRolling.stayTargets soko2_2.board 67 .south).all (fun landing => !pushGuard support p 45 67 89 landing || decide (bonus 45 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 67 + bonus 67 (change p 67 (some landing)))) && (pushTargets soko2_2.board 67 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 45 67 89 landing || decide (bonus 45 p ≤ 1 - Generated.soko2_2Potential.boulder 67 - Generated.soko2_2Potential.hole landing + bonus 67 (change p 67 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check28 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check29 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir45_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 .east p = true := by
  change ((!walkGuard soko2_2.board support p 45 46 .east || decide (bonus 45 p ≤ bonus 46 p)) && ((PreciseRolling.stayTargets soko2_2.board 46 .east).all (fun landing => !pushGuard support p 45 46 47 landing || decide (bonus 45 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 46 + bonus 46 (change p 46 (some landing)))) && (pushTargets soko2_2.board 46 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 45 46 47 landing || decide (bonus 45 p ≤ 1 - Generated.soko2_2Potential.boulder 46 - Generated.soko2_2Potential.hole landing + bonus 46 (change p 46 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check30 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check31 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir45_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 .west p = true := by
  rfl
theorem dir45_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 .northEast p = true := by
  rfl
theorem dir45_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 .northWest p = true := by
  rfl
theorem dir45_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 .southEast p = true := by
  rfl
theorem dir45_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 45 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
