import NetHack.Sokoban22Refined85.Directions08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir125_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 .north p = true := by
  change ((!walkGuard soko2_2.board support p 125 103 .north || decide (bonus 125 p ≤ bonus 103 p)) && ((PreciseRolling.stayTargets soko2_2.board 103 .north).all (fun landing => !pushGuard support p 125 103 81 landing || decide (bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some landing)))) && (pushTargets soko2_2.board 103 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 125 103 81 landing || decide (bonus 125 p ≤ 1 - Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.hole landing + bonus 103 (change p 103 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check410 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check411 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir125_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 .south p = true := by
  change ((!walkGuard soko2_2.board support p 125 147 .south || decide (bonus 125 p ≤ bonus 147 p)) && ((PreciseRolling.stayTargets soko2_2.board 147 .south).all (fun landing => !pushGuard support p 125 147 169 landing || decide (bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some landing)))) && (pushTargets soko2_2.board 147 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 125 147 169 landing || decide (bonus 125 p ≤ 1 - Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.hole landing + bonus 147 (change p 147 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check412 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check413 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir125_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 .east p = true := by
  change ((!walkGuard soko2_2.board support p 125 126 .east || decide (bonus 125 p ≤ bonus 126 p)) && ((PreciseRolling.stayTargets soko2_2.board 126 .east).all (fun landing => !pushGuard support p 125 126 127 landing || decide (bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some landing)))) && (pushTargets soko2_2.board 126 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 125 126 127 landing || decide (bonus 125 p ≤ 1 - Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.hole landing + bonus 126 (change p 126 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check414 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check415 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir125_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 .west p = true := by
  change ((!walkGuard soko2_2.board support p 125 124 .west || decide (bonus 125 p ≤ bonus 124 p)) && ((PreciseRolling.stayTargets soko2_2.board 124 .west).all (fun landing => !pushGuard support p 125 124 123 landing || decide (bonus 125 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some landing)))) && (pushTargets soko2_2.board 124 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 125 124 123 landing || decide (bonus 125 p ≤ 1 - Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.hole landing + bonus 124 (change p 124 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check416 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check417 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir125_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 125 104 .northEast || decide (bonus 125 p ≤ bonus 104 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check418 p, rfl⟩
theorem dir125_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 125 102 .northWest || decide (bonus 125 p ≤ bonus 102 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check419 p, rfl⟩
theorem dir125_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 125 148 .southEast || decide (bonus 125 p ≤ bonus 148 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check420 p, rfl⟩
theorem dir125_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 125 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 125 146 .southWest || decide (bonus 125 p ≤ bonus 146 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check421 p, rfl⟩
theorem dir126_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 .north p = true := by
  change ((!walkGuard soko2_2.board support p 126 104 .north || decide (bonus 126 p ≤ bonus 104 p)) && ((PreciseRolling.stayTargets soko2_2.board 104 .north).all (fun landing => !pushGuard support p 126 104 82 landing || decide (bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some landing)))) && (pushTargets soko2_2.board 104 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 126 104 82 landing || decide (bonus 126 p ≤ 1 - Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.hole landing + bonus 104 (change p 104 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check422 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check423 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir126_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 .south p = true := by
  change ((!walkGuard soko2_2.board support p 126 148 .south || decide (bonus 126 p ≤ bonus 148 p)) && ((PreciseRolling.stayTargets soko2_2.board 148 .south).all (fun landing => !pushGuard support p 126 148 170 landing || decide (bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some landing)))) && (pushTargets soko2_2.board 148 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 126 148 170 landing || decide (bonus 126 p ≤ 1 - Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.hole landing + bonus 148 (change p 148 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check424 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check425 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir126_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 .east p = true := by
  change ((!walkGuard soko2_2.board support p 126 127 .east || decide (bonus 126 p ≤ bonus 127 p)) && ((PreciseRolling.stayTargets soko2_2.board 127 .east).all (fun landing => !pushGuard support p 126 127 128 landing || decide (bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some landing)))) && (pushTargets soko2_2.board 127 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 126 127 128 landing || decide (bonus 126 p ≤ 1 - Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.hole landing + bonus 127 (change p 127 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check426 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check427 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir126_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 .west p = true := by
  change ((!walkGuard soko2_2.board support p 126 125 .west || decide (bonus 126 p ≤ bonus 125 p)) && ((PreciseRolling.stayTargets soko2_2.board 125 .west).all (fun landing => !pushGuard support p 126 125 124 landing || decide (bonus 126 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some landing)))) && (pushTargets soko2_2.board 125 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 126 125 124 landing || decide (bonus 126 p ≤ 1 - Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.hole landing + bonus 125 (change p 125 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check428 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check429 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir126_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 126 105 .northEast || decide (bonus 126 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check430 p, rfl⟩
theorem dir126_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 126 103 .northWest || decide (bonus 126 p ≤ bonus 103 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check431 p, rfl⟩
theorem dir126_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 126 149 .southEast || decide (bonus 126 p ≤ bonus 149 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check432 p, rfl⟩
theorem dir126_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 126 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 126 147 .southWest || decide (bonus 126 p ≤ bonus 147 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check433 p, rfl⟩
theorem dir127_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 .north p = true := by
  change ((!walkGuard soko2_2.board support p 127 105 .north || decide (bonus 127 p ≤ bonus 105 p)) && ((PreciseRolling.stayTargets soko2_2.board 105 .north).all (fun landing => !pushGuard support p 127 105 83 landing || decide (bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some landing)))) && (pushTargets soko2_2.board 105 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 127 105 83 landing || decide (bonus 127 p ≤ 1 - Generated.soko2_2Potential.boulder 105 - Generated.soko2_2Potential.hole landing + bonus 105 (change p 105 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check434 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check435 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir127_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 .south p = true := by
  change ((!walkGuard soko2_2.board support p 127 149 .south || decide (bonus 127 p ≤ bonus 149 p)) && ((PreciseRolling.stayTargets soko2_2.board 149 .south).all (fun landing => !pushGuard support p 127 149 171 landing || decide (bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some landing)))) && (pushTargets soko2_2.board 149 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 127 149 171 landing || decide (bonus 127 p ≤ 1 - Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.hole landing + bonus 149 (change p 149 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check436 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check437 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir127_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 .east p = true := by
  change ((!walkGuard soko2_2.board support p 127 128 .east || decide (bonus 127 p ≤ bonus 128 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check438 p, rfl⟩
theorem dir127_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 .west p = true := by
  change ((!walkGuard soko2_2.board support p 127 126 .west || decide (bonus 127 p ≤ bonus 126 p)) && ((PreciseRolling.stayTargets soko2_2.board 126 .west).all (fun landing => !pushGuard support p 127 126 125 landing || decide (bonus 127 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some landing)))) && (pushTargets soko2_2.board 126 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 127 126 125 landing || decide (bonus 127 p ≤ 1 - Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.hole landing + bonus 126 (change p 126 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check439 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check440 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir127_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 127 106 .northEast || decide (bonus 127 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check441 p, rfl⟩
theorem dir127_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 127 104 .northWest || decide (bonus 127 p ≤ bonus 104 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check442 p, rfl⟩
theorem dir127_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 127 150 .southEast || decide (bonus 127 p ≤ bonus 150 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check443 p, rfl⟩
theorem dir127_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 127 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 127 148 .southWest || decide (bonus 127 p ≤ bonus 148 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check444 p, rfl⟩
theorem dir128_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 .north p = true := by
  change ((!walkGuard soko2_2.board support p 128 106 .north || decide (bonus 128 p ≤ bonus 106 p)) && ((PreciseRolling.stayTargets soko2_2.board 106 .north).all (fun landing => !pushGuard support p 128 106 84 landing || decide (bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 106 + bonus 106 (change p 106 (some landing)))) && (pushTargets soko2_2.board 106 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 128 106 84 landing || decide (bonus 128 p ≤ 1 - Generated.soko2_2Potential.boulder 106 - Generated.soko2_2Potential.hole landing + bonus 106 (change p 106 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check445 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check446 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir128_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 .south p = true := by
  change ((!walkGuard soko2_2.board support p 128 150 .south || decide (bonus 128 p ≤ bonus 150 p)) && ((PreciseRolling.stayTargets soko2_2.board 150 .south).all (fun landing => !pushGuard support p 128 150 172 landing || decide (bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 150 + bonus 150 (change p 150 (some landing)))) && (pushTargets soko2_2.board 150 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 128 150 172 landing || decide (bonus 128 p ≤ 1 - Generated.soko2_2Potential.boulder 150 - Generated.soko2_2Potential.hole landing + bonus 150 (change p 150 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check447 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check448 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir128_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 .east p = true := by
  rfl
theorem dir128_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 .west p = true := by
  change ((!walkGuard soko2_2.board support p 128 127 .west || decide (bonus 128 p ≤ bonus 127 p)) && ((PreciseRolling.stayTargets soko2_2.board 127 .west).all (fun landing => !pushGuard support p 128 127 126 landing || decide (bonus 128 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some landing)))) && (pushTargets soko2_2.board 127 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 128 127 126 landing || decide (bonus 128 p ≤ 1 - Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.hole landing + bonus 127 (change p 127 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check449 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check450 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir128_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 .northEast p = true := by
  rfl
theorem dir128_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 128 105 .northWest || decide (bonus 128 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check451 p, rfl⟩
theorem dir128_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 .southEast p = true := by
  rfl
theorem dir128_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 128 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 128 149 .southWest || decide (bonus 128 p ≤ bonus 149 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check452 p, rfl⟩
theorem dir133_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 .north p = true := by
  change ((!walkGuard soko2_2.board support p 133 111 .north || decide (bonus 133 p ≤ bonus 111 p)) && ((PreciseRolling.stayTargets soko2_2.board 111 .north).all (fun landing => !pushGuard support p 133 111 89 landing || decide (bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 111 + bonus 111 (change p 111 (some landing)))) && (pushTargets soko2_2.board 111 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 133 111 89 landing || decide (bonus 133 p ≤ 1 - Generated.soko2_2Potential.boulder 111 - Generated.soko2_2Potential.hole landing + bonus 111 (change p 111 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check453 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check454 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir133_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 .south p = true := by
  change ((!walkGuard soko2_2.board support p 133 155 .south || decide (bonus 133 p ≤ bonus 155 p)) && ((PreciseRolling.stayTargets soko2_2.board 155 .south).all (fun landing => !pushGuard support p 133 155 177 landing || decide (bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 155 + bonus 155 (change p 155 (some landing)))) && (pushTargets soko2_2.board 155 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 133 155 177 landing || decide (bonus 133 p ≤ 1 - Generated.soko2_2Potential.boulder 155 - Generated.soko2_2Potential.hole landing + bonus 155 (change p 155 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check455 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check456 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir133_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 .east p = true := by
  change ((!walkGuard soko2_2.board support p 133 134 .east || decide (bonus 133 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko2_2.board 134 .east).all (fun landing => !pushGuard support p 133 134 135 landing || decide (bonus 133 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko2_2.board 134 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 133 134 135 landing || decide (bonus 133 p ≤ 1 - Generated.soko2_2Potential.boulder 134 - Generated.soko2_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check457 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check458 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir133_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 .west p = true := by
  rfl
theorem dir133_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 .northEast p = true := by
  rfl
theorem dir133_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 .northWest p = true := by
  rfl
theorem dir133_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 133 156 .southEast || decide (bonus 133 p ≤ bonus 156 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check459 p, rfl⟩
theorem dir133_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 133 .southWest p = true := by
  rfl
theorem dir134_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 .north p = true := by
  rfl
theorem dir134_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 .south p = true := by
  change ((!walkGuard soko2_2.board support p 134 156 .south || decide (bonus 134 p ≤ bonus 156 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check460 p, rfl⟩
theorem dir134_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 .east p = true := by
  change ((!walkGuard soko2_2.board support p 134 135 .east || decide (bonus 134 p ≤ bonus 135 p)) && ((PreciseRolling.stayTargets soko2_2.board 135 .east).all (fun landing => !pushGuard support p 134 135 136 landing || decide (bonus 134 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some landing)))) && (pushTargets soko2_2.board 135 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 134 135 136 landing || decide (bonus 134 p ≤ 1 - Generated.soko2_2Potential.boulder 135 - Generated.soko2_2Potential.hole landing + bonus 135 (change p 135 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check461 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check462 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir134_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 .west p = true := by
  change ((!walkGuard soko2_2.board support p 134 133 .west || decide (bonus 134 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check463 p, rfl⟩
theorem dir134_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 134 113 .northEast || decide (bonus 134 p ≤ bonus 113 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check464 p, rfl⟩
theorem dir134_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 134 111 .northWest || decide (bonus 134 p ≤ bonus 111 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check465 p, rfl⟩
theorem dir134_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 134 157 .southEast || decide (bonus 134 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check466 p, rfl⟩
theorem dir134_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 134 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 134 155 .southWest || decide (bonus 134 p ≤ bonus 155 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check467 p, rfl⟩
end NetHack.Sokoban22Refined85
