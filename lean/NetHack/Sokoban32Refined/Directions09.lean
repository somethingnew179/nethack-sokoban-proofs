import NetHack.Sokoban32Refined.Directions08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir123_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 .north p = true := by
  change ((!walkGuard soko3_2.board support p 123 97 .north || decide (bonus 123 p ≤ bonus 97 p)) && ((PreciseRolling.stayTargets soko3_2.board 97 .north).all (fun landing => !pushGuard support p 123 97 71 landing || decide (bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some landing)))) && (pushTargets soko3_2.board 97 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 123 97 71 landing || decide (bonus 123 p ≤ 1 - Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.hole landing + bonus 97 (change p 97 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check421 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check422 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir123_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 .south p = true := by
  change ((!walkGuard soko3_2.board support p 123 149 .south || decide (bonus 123 p ≤ bonus 149 p)) && ((PreciseRolling.stayTargets soko3_2.board 149 .south).all (fun landing => !pushGuard support p 123 149 175 landing || decide (bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some landing)))) && (pushTargets soko3_2.board 149 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 123 149 175 landing || decide (bonus 123 p ≤ 1 - Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.hole landing + bonus 149 (change p 149 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check423 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check424 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir123_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 .east p = true := by
  change ((!walkGuard soko3_2.board support p 123 124 .east || decide (bonus 123 p ≤ bonus 124 p)) && ((PreciseRolling.stayTargets soko3_2.board 124 .east).all (fun landing => !pushGuard support p 123 124 125 landing || decide (bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some landing)))) && (pushTargets soko3_2.board 124 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 123 124 125 landing || decide (bonus 123 p ≤ 1 - Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.hole landing + bonus 124 (change p 124 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check425 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check426 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir123_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 .west p = true := by
  change ((!walkGuard soko3_2.board support p 123 122 .west || decide (bonus 123 p ≤ bonus 122 p)) && ((PreciseRolling.stayTargets soko3_2.board 122 .west).all (fun landing => !pushGuard support p 123 122 121 landing || decide (bonus 123 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some landing)))) && (pushTargets soko3_2.board 122 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 123 122 121 landing || decide (bonus 123 p ≤ 1 - Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.hole landing + bonus 122 (change p 122 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check427 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check428 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir123_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 123 98 .northEast || decide (bonus 123 p ≤ bonus 98 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check429 p, rfl⟩
theorem dir123_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 123 96 .northWest || decide (bonus 123 p ≤ bonus 96 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check430 p, rfl⟩
theorem dir123_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 123 150 .southEast || decide (bonus 123 p ≤ bonus 150 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check431 p, rfl⟩
theorem dir123_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 123 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 123 148 .southWest || decide (bonus 123 p ≤ bonus 148 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check432 p, rfl⟩
theorem dir124_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 .north p = true := by
  change ((!walkGuard soko3_2.board support p 124 98 .north || decide (bonus 124 p ≤ bonus 98 p)) && ((PreciseRolling.stayTargets soko3_2.board 98 .north).all (fun landing => !pushGuard support p 124 98 72 landing || decide (bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some landing)))) && (pushTargets soko3_2.board 98 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 124 98 72 landing || decide (bonus 124 p ≤ 1 - Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.hole landing + bonus 98 (change p 98 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check433 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check434 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir124_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 .south p = true := by
  change ((!walkGuard soko3_2.board support p 124 150 .south || decide (bonus 124 p ≤ bonus 150 p)) && ((PreciseRolling.stayTargets soko3_2.board 150 .south).all (fun landing => !pushGuard support p 124 150 176 landing || decide (bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some landing)))) && (pushTargets soko3_2.board 150 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 124 150 176 landing || decide (bonus 124 p ≤ 1 - Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.hole landing + bonus 150 (change p 150 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check435 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check436 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir124_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 .east p = true := by
  change ((!walkGuard soko3_2.board support p 124 125 .east || decide (bonus 124 p ≤ bonus 125 p)) && ((PreciseRolling.stayTargets soko3_2.board 125 .east).all (fun landing => !pushGuard support p 124 125 126 landing || decide (bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some landing)))) && (pushTargets soko3_2.board 125 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 124 125 126 landing || decide (bonus 124 p ≤ 1 - Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.hole landing + bonus 125 (change p 125 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check437 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check438 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir124_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 .west p = true := by
  change ((!walkGuard soko3_2.board support p 124 123 .west || decide (bonus 124 p ≤ bonus 123 p)) && ((PreciseRolling.stayTargets soko3_2.board 123 .west).all (fun landing => !pushGuard support p 124 123 122 landing || decide (bonus 124 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some landing)))) && (pushTargets soko3_2.board 123 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 124 123 122 landing || decide (bonus 124 p ≤ 1 - Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.hole landing + bonus 123 (change p 123 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check439 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check440 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir124_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 124 99 .northEast || decide (bonus 124 p ≤ bonus 99 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check441 p, rfl⟩
theorem dir124_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 124 97 .northWest || decide (bonus 124 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check442 p, rfl⟩
theorem dir124_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 124 151 .southEast || decide (bonus 124 p ≤ bonus 151 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check443 p, rfl⟩
theorem dir124_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 124 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 124 149 .southWest || decide (bonus 124 p ≤ bonus 149 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check444 p, rfl⟩
theorem dir125_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 .north p = true := by
  change ((!walkGuard soko3_2.board support p 125 99 .north || decide (bonus 125 p ≤ bonus 99 p)) && ((PreciseRolling.stayTargets soko3_2.board 99 .north).all (fun landing => !pushGuard support p 125 99 73 landing || decide (bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some landing)))) && (pushTargets soko3_2.board 99 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 125 99 73 landing || decide (bonus 125 p ≤ 1 - Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.hole landing + bonus 99 (change p 99 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check445 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check446 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir125_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 .south p = true := by
  change ((!walkGuard soko3_2.board support p 125 151 .south || decide (bonus 125 p ≤ bonus 151 p)) && ((PreciseRolling.stayTargets soko3_2.board 151 .south).all (fun landing => !pushGuard support p 125 151 177 landing || decide (bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some landing)))) && (pushTargets soko3_2.board 151 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 125 151 177 landing || decide (bonus 125 p ≤ 1 - Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.hole landing + bonus 151 (change p 151 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check447 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check448 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir125_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 .east p = true := by
  change ((!walkGuard soko3_2.board support p 125 126 .east || decide (bonus 125 p ≤ bonus 126 p)) && ((PreciseRolling.stayTargets soko3_2.board 126 .east).all (fun landing => !pushGuard support p 125 126 127 landing || decide (bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some landing)))) && (pushTargets soko3_2.board 126 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 125 126 127 landing || decide (bonus 125 p ≤ 1 - Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.hole landing + bonus 126 (change p 126 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check449 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check450 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir125_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 .west p = true := by
  change ((!walkGuard soko3_2.board support p 125 124 .west || decide (bonus 125 p ≤ bonus 124 p)) && ((PreciseRolling.stayTargets soko3_2.board 124 .west).all (fun landing => !pushGuard support p 125 124 123 landing || decide (bonus 125 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some landing)))) && (pushTargets soko3_2.board 124 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 125 124 123 landing || decide (bonus 125 p ≤ 1 - Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.hole landing + bonus 124 (change p 124 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check451 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check452 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir125_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 125 100 .northEast || decide (bonus 125 p ≤ bonus 100 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check453 p, rfl⟩
theorem dir125_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 125 98 .northWest || decide (bonus 125 p ≤ bonus 98 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check454 p, rfl⟩
theorem dir125_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 125 152 .southEast || decide (bonus 125 p ≤ bonus 152 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check455 p, rfl⟩
theorem dir125_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 125 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 125 150 .southWest || decide (bonus 125 p ≤ bonus 150 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check456 p, rfl⟩
theorem dir126_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 .north p = true := by
  change ((!walkGuard soko3_2.board support p 126 100 .north || decide (bonus 126 p ≤ bonus 100 p)) && ((PreciseRolling.stayTargets soko3_2.board 100 .north).all (fun landing => !pushGuard support p 126 100 74 landing || decide (bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some landing)))) && (pushTargets soko3_2.board 100 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 126 100 74 landing || decide (bonus 126 p ≤ 1 - Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.hole landing + bonus 100 (change p 100 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check457 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check458 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir126_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 .south p = true := by
  change ((!walkGuard soko3_2.board support p 126 152 .south || decide (bonus 126 p ≤ bonus 152 p)) && ((PreciseRolling.stayTargets soko3_2.board 152 .south).all (fun landing => !pushGuard support p 126 152 178 landing || decide (bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some landing)))) && (pushTargets soko3_2.board 152 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 126 152 178 landing || decide (bonus 126 p ≤ 1 - Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.hole landing + bonus 152 (change p 152 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check459 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check460 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir126_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 .east p = true := by
  change ((!walkGuard soko3_2.board support p 126 127 .east || decide (bonus 126 p ≤ bonus 127 p)) && ((PreciseRolling.stayTargets soko3_2.board 127 .east).all (fun landing => !pushGuard support p 126 127 128 landing || decide (bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some landing)))) && (pushTargets soko3_2.board 127 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 126 127 128 landing || decide (bonus 126 p ≤ 1 - Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.hole landing + bonus 127 (change p 127 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check461 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check462 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir126_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 .west p = true := by
  change ((!walkGuard soko3_2.board support p 126 125 .west || decide (bonus 126 p ≤ bonus 125 p)) && ((PreciseRolling.stayTargets soko3_2.board 125 .west).all (fun landing => !pushGuard support p 126 125 124 landing || decide (bonus 126 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some landing)))) && (pushTargets soko3_2.board 125 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 126 125 124 landing || decide (bonus 126 p ≤ 1 - Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.hole landing + bonus 125 (change p 125 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check463 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check464 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir126_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 126 101 .northEast || decide (bonus 126 p ≤ bonus 101 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check465 p, rfl⟩
theorem dir126_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 126 99 .northWest || decide (bonus 126 p ≤ bonus 99 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check466 p, rfl⟩
theorem dir126_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 126 153 .southEast || decide (bonus 126 p ≤ bonus 153 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check467 p, rfl⟩
theorem dir126_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 126 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 126 151 .southWest || decide (bonus 126 p ≤ bonus 151 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check468 p, rfl⟩
theorem dir127_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 .north p = true := by
  change ((!walkGuard soko3_2.board support p 127 101 .north || decide (bonus 127 p ≤ bonus 101 p)) && ((PreciseRolling.stayTargets soko3_2.board 101 .north).all (fun landing => !pushGuard support p 127 101 75 landing || decide (bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some landing)))) && (pushTargets soko3_2.board 101 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 127 101 75 landing || decide (bonus 127 p ≤ 1 - Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.hole landing + bonus 101 (change p 101 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check469 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check470 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir127_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 .south p = true := by
  change ((!walkGuard soko3_2.board support p 127 153 .south || decide (bonus 127 p ≤ bonus 153 p)) && ((PreciseRolling.stayTargets soko3_2.board 153 .south).all (fun landing => !pushGuard support p 127 153 179 landing || decide (bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some landing)))) && (pushTargets soko3_2.board 153 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 127 153 179 landing || decide (bonus 127 p ≤ 1 - Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.hole landing + bonus 153 (change p 153 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check471 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check472 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir127_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 .east p = true := by
  change ((!walkGuard soko3_2.board support p 127 128 .east || decide (bonus 127 p ≤ bonus 128 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check473 p, rfl⟩
theorem dir127_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 .west p = true := by
  change ((!walkGuard soko3_2.board support p 127 126 .west || decide (bonus 127 p ≤ bonus 126 p)) && ((PreciseRolling.stayTargets soko3_2.board 126 .west).all (fun landing => !pushGuard support p 127 126 125 landing || decide (bonus 127 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some landing)))) && (pushTargets soko3_2.board 126 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 127 126 125 landing || decide (bonus 127 p ≤ 1 - Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.hole landing + bonus 126 (change p 126 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check474 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check475 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir127_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 127 102 .northEast || decide (bonus 127 p ≤ bonus 102 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check476 p, rfl⟩
theorem dir127_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 127 100 .northWest || decide (bonus 127 p ≤ bonus 100 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check477 p, rfl⟩
theorem dir127_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 127 154 .southEast || decide (bonus 127 p ≤ bonus 154 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check478 p, rfl⟩
theorem dir127_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 127 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 127 152 .southWest || decide (bonus 127 p ≤ bonus 152 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check479 p, rfl⟩
theorem dir128_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 .north p = true := by
  change ((!walkGuard soko3_2.board support p 128 102 .north || decide (bonus 128 p ≤ bonus 102 p)) && ((PreciseRolling.stayTargets soko3_2.board 102 .north).all (fun landing => !pushGuard support p 128 102 76 landing || decide (bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 102 + bonus 102 (change p 102 (some landing)))) && (pushTargets soko3_2.board 102 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 128 102 76 landing || decide (bonus 128 p ≤ 1 - Generated.soko3_2Potential.boulder 102 - Generated.soko3_2Potential.hole landing + bonus 102 (change p 102 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check480 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check481 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir128_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 .south p = true := by
  change ((!walkGuard soko3_2.board support p 128 154 .south || decide (bonus 128 p ≤ bonus 154 p)) && ((PreciseRolling.stayTargets soko3_2.board 154 .south).all (fun landing => !pushGuard support p 128 154 180 landing || decide (bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 154 + bonus 154 (change p 154 (some landing)))) && (pushTargets soko3_2.board 154 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 128 154 180 landing || decide (bonus 128 p ≤ 1 - Generated.soko3_2Potential.boulder 154 - Generated.soko3_2Potential.hole landing + bonus 154 (change p 154 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check482 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check483 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir128_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 .east p = true := by
  rfl
theorem dir128_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 .west p = true := by
  change ((!walkGuard soko3_2.board support p 128 127 .west || decide (bonus 128 p ≤ bonus 127 p)) && ((PreciseRolling.stayTargets soko3_2.board 127 .west).all (fun landing => !pushGuard support p 128 127 126 landing || decide (bonus 128 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some landing)))) && (pushTargets soko3_2.board 127 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 128 127 126 landing || decide (bonus 128 p ≤ 1 - Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.hole landing + bonus 127 (change p 127 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check484 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check485 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir128_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 .northEast p = true := by
  rfl
theorem dir128_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 128 101 .northWest || decide (bonus 128 p ≤ bonus 101 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check486 p, rfl⟩
theorem dir128_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 .southEast p = true := by
  rfl
theorem dir128_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 128 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 128 153 .southWest || decide (bonus 128 p ≤ bonus 153 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check487 p, rfl⟩
end NetHack.Sokoban32Refined
