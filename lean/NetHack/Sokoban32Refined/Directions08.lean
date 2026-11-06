import NetHack.Sokoban32Refined.Directions07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir112_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 .north p = true := by
  change ((!walkGuard soko3_2.board support p 112 86 .north || decide (bonus 112 p ≤ bonus 86 p)) && ((PreciseRolling.stayTargets soko3_2.board 86 .north).all (fun landing => !pushGuard support p 112 86 60 landing || decide (bonus 112 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 86 + bonus 86 (change p 86 (some landing)))) && (pushTargets soko3_2.board 86 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 112 86 60 landing || decide (bonus 112 p ≤ 1 - Generated.soko3_2Potential.boulder 86 - Generated.soko3_2Potential.hole landing + bonus 86 (change p 86 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check371 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check372 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir112_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 .south p = true := by
  change ((!walkGuard soko3_2.board support p 112 138 .south || decide (bonus 112 p ≤ bonus 138 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check373 p, rfl⟩
theorem dir112_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 .east p = true := by
  change ((!walkGuard soko3_2.board support p 112 113 .east || decide (bonus 112 p ≤ bonus 113 p)) && ((PreciseRolling.stayTargets soko3_2.board 113 .east).all (fun landing => !pushGuard support p 112 113 114 landing || decide (bonus 112 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 113 + bonus 113 (change p 113 (some landing)))) && (pushTargets soko3_2.board 113 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 112 113 114 landing || decide (bonus 112 p ≤ 1 - Generated.soko3_2Potential.boulder 113 - Generated.soko3_2Potential.hole landing + bonus 113 (change p 113 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check374 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check375 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir112_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 .west p = true := by
  rfl
theorem dir112_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 .northEast p = true := by
  rfl
theorem dir112_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 .northWest p = true := by
  rfl
theorem dir112_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 112 139 .southEast || decide (bonus 112 p ≤ bonus 139 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check376 p, rfl⟩
theorem dir112_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 112 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 112 137 .southWest || decide (bonus 112 p ≤ bonus 137 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check377 p, rfl⟩
theorem dir113_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 .north p = true := by
  rfl
theorem dir113_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 .south p = true := by
  change ((!walkGuard soko3_2.board support p 113 139 .south || decide (bonus 113 p ≤ bonus 139 p)) && ((PreciseRolling.stayTargets soko3_2.board 139 .south).all (fun landing => !pushGuard support p 113 139 165 landing || decide (bonus 113 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 139 + bonus 139 (change p 139 (some landing)))) && (pushTargets soko3_2.board 139 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 113 139 165 landing || decide (bonus 113 p ≤ 1 - Generated.soko3_2Potential.boulder 139 - Generated.soko3_2Potential.hole landing + bonus 139 (change p 139 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check378 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check379 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir113_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 .east p = true := by
  change ((!walkGuard soko3_2.board support p 113 114 .east || decide (bonus 113 p ≤ bonus 114 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check380 p, rfl⟩
theorem dir113_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 .west p = true := by
  change ((!walkGuard soko3_2.board support p 113 112 .west || decide (bonus 113 p ≤ bonus 112 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check381 p, rfl⟩
theorem dir113_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 113 88 .northEast || decide (bonus 113 p ≤ bonus 88 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check382 p, rfl⟩
theorem dir113_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 113 86 .northWest || decide (bonus 113 p ≤ bonus 86 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check383 p, rfl⟩
theorem dir113_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 .southEast p = true := by
  rfl
theorem dir113_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 113 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 113 138 .southWest || decide (bonus 113 p ≤ bonus 138 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check384 p, rfl⟩
theorem dir114_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 .north p = true := by
  change ((!walkGuard soko3_2.board support p 114 88 .north || decide (bonus 114 p ≤ bonus 88 p)) && ((PreciseRolling.stayTargets soko3_2.board 88 .north).all (fun landing => !pushGuard support p 114 88 62 landing || decide (bonus 114 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 88 + bonus 88 (change p 88 (some landing)))) && (pushTargets soko3_2.board 88 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 114 88 62 landing || decide (bonus 114 p ≤ 1 - Generated.soko3_2Potential.boulder 88 - Generated.soko3_2Potential.hole landing + bonus 88 (change p 88 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check385 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check386 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir114_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 .south p = true := by
  rfl
theorem dir114_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 .east p = true := by
  rfl
theorem dir114_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 .west p = true := by
  change ((!walkGuard soko3_2.board support p 114 113 .west || decide (bonus 114 p ≤ bonus 113 p)) && ((PreciseRolling.stayTargets soko3_2.board 113 .west).all (fun landing => !pushGuard support p 114 113 112 landing || decide (bonus 114 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 113 + bonus 113 (change p 113 (some landing)))) && (pushTargets soko3_2.board 113 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 114 113 112 landing || decide (bonus 114 p ≤ 1 - Generated.soko3_2Potential.boulder 113 - Generated.soko3_2Potential.hole landing + bonus 113 (change p 113 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check387 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check388 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir114_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 .northEast p = true := by
  rfl
theorem dir114_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 .northWest p = true := by
  rfl
theorem dir114_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 .southEast p = true := by
  rfl
theorem dir114_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 114 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 114 139 .southWest || decide (bonus 114 p ≤ bonus 139 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check389 p, rfl⟩
theorem dir120_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 .north p = true := by
  change ((!walkGuard soko3_2.board support p 120 94 .north || decide (bonus 120 p ≤ bonus 94 p)) && ((PreciseRolling.stayTargets soko3_2.board 94 .north).all (fun landing => !pushGuard support p 120 94 68 landing || decide (bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 94 + bonus 94 (change p 94 (some landing)))) && (pushTargets soko3_2.board 94 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 120 94 68 landing || decide (bonus 120 p ≤ 1 - Generated.soko3_2Potential.boulder 94 - Generated.soko3_2Potential.hole landing + bonus 94 (change p 94 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check390 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check391 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir120_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 .south p = true := by
  change ((!walkGuard soko3_2.board support p 120 146 .south || decide (bonus 120 p ≤ bonus 146 p)) && ((PreciseRolling.stayTargets soko3_2.board 146 .south).all (fun landing => !pushGuard support p 120 146 172 landing || decide (bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 146 + bonus 146 (change p 146 (some landing)))) && (pushTargets soko3_2.board 146 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 120 146 172 landing || decide (bonus 120 p ≤ 1 - Generated.soko3_2Potential.boulder 146 - Generated.soko3_2Potential.hole landing + bonus 146 (change p 146 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check392 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check393 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir120_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 .east p = true := by
  change ((!walkGuard soko3_2.board support p 120 121 .east || decide (bonus 120 p ≤ bonus 121 p)) && ((PreciseRolling.stayTargets soko3_2.board 121 .east).all (fun landing => !pushGuard support p 120 121 122 landing || decide (bonus 120 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some landing)))) && (pushTargets soko3_2.board 121 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 120 121 122 landing || decide (bonus 120 p ≤ 1 - Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.hole landing + bonus 121 (change p 121 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check394 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check395 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir120_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 .west p = true := by
  rfl
theorem dir120_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 120 95 .northEast || decide (bonus 120 p ≤ bonus 95 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check396 p, rfl⟩
theorem dir120_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 .northWest p = true := by
  rfl
theorem dir120_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 120 147 .southEast || decide (bonus 120 p ≤ bonus 147 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check397 p, rfl⟩
theorem dir120_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 120 .southWest p = true := by
  rfl
theorem dir121_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 .north p = true := by
  change ((!walkGuard soko3_2.board support p 121 95 .north || decide (bonus 121 p ≤ bonus 95 p)) && ((PreciseRolling.stayTargets soko3_2.board 95 .north).all (fun landing => !pushGuard support p 121 95 69 landing || decide (bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some landing)))) && (pushTargets soko3_2.board 95 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 121 95 69 landing || decide (bonus 121 p ≤ 1 - Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.hole landing + bonus 95 (change p 95 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check398 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check399 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir121_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 .south p = true := by
  change ((!walkGuard soko3_2.board support p 121 147 .south || decide (bonus 121 p ≤ bonus 147 p)) && ((PreciseRolling.stayTargets soko3_2.board 147 .south).all (fun landing => !pushGuard support p 121 147 173 landing || decide (bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some landing)))) && (pushTargets soko3_2.board 147 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 121 147 173 landing || decide (bonus 121 p ≤ 1 - Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.hole landing + bonus 147 (change p 147 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check400 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check401 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir121_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 .east p = true := by
  change ((!walkGuard soko3_2.board support p 121 122 .east || decide (bonus 121 p ≤ bonus 122 p)) && ((PreciseRolling.stayTargets soko3_2.board 122 .east).all (fun landing => !pushGuard support p 121 122 123 landing || decide (bonus 121 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some landing)))) && (pushTargets soko3_2.board 122 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 121 122 123 landing || decide (bonus 121 p ≤ 1 - Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.hole landing + bonus 122 (change p 122 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check402 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check403 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir121_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 .west p = true := by
  change ((!walkGuard soko3_2.board support p 121 120 .west || decide (bonus 121 p ≤ bonus 120 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check404 p, rfl⟩
theorem dir121_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 121 96 .northEast || decide (bonus 121 p ≤ bonus 96 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check405 p, rfl⟩
theorem dir121_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 121 94 .northWest || decide (bonus 121 p ≤ bonus 94 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check406 p, rfl⟩
theorem dir121_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 121 148 .southEast || decide (bonus 121 p ≤ bonus 148 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check407 p, rfl⟩
theorem dir121_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 121 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 121 146 .southWest || decide (bonus 121 p ≤ bonus 146 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check408 p, rfl⟩
theorem dir122_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 .north p = true := by
  change ((!walkGuard soko3_2.board support p 122 96 .north || decide (bonus 122 p ≤ bonus 96 p)) && ((PreciseRolling.stayTargets soko3_2.board 96 .north).all (fun landing => !pushGuard support p 122 96 70 landing || decide (bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some landing)))) && (pushTargets soko3_2.board 96 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 122 96 70 landing || decide (bonus 122 p ≤ 1 - Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.hole landing + bonus 96 (change p 96 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check409 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check410 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir122_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 .south p = true := by
  change ((!walkGuard soko3_2.board support p 122 148 .south || decide (bonus 122 p ≤ bonus 148 p)) && ((PreciseRolling.stayTargets soko3_2.board 148 .south).all (fun landing => !pushGuard support p 122 148 174 landing || decide (bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some landing)))) && (pushTargets soko3_2.board 148 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 122 148 174 landing || decide (bonus 122 p ≤ 1 - Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.hole landing + bonus 148 (change p 148 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check411 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check412 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir122_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 .east p = true := by
  change ((!walkGuard soko3_2.board support p 122 123 .east || decide (bonus 122 p ≤ bonus 123 p)) && ((PreciseRolling.stayTargets soko3_2.board 123 .east).all (fun landing => !pushGuard support p 122 123 124 landing || decide (bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some landing)))) && (pushTargets soko3_2.board 123 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 122 123 124 landing || decide (bonus 122 p ≤ 1 - Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.hole landing + bonus 123 (change p 123 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check413 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check414 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir122_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 .west p = true := by
  change ((!walkGuard soko3_2.board support p 122 121 .west || decide (bonus 122 p ≤ bonus 121 p)) && ((PreciseRolling.stayTargets soko3_2.board 121 .west).all (fun landing => !pushGuard support p 122 121 120 landing || decide (bonus 122 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some landing)))) && (pushTargets soko3_2.board 121 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 122 121 120 landing || decide (bonus 122 p ≤ 1 - Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.hole landing + bonus 121 (change p 121 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check415 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check416 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir122_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 122 97 .northEast || decide (bonus 122 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check417 p, rfl⟩
theorem dir122_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 122 95 .northWest || decide (bonus 122 p ≤ bonus 95 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check418 p, rfl⟩
theorem dir122_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 122 149 .southEast || decide (bonus 122 p ≤ bonus 149 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check419 p, rfl⟩
theorem dir122_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 122 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 122 147 .southWest || decide (bonus 122 p ≤ bonus 147 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check420 p, rfl⟩
end NetHack.Sokoban32Refined
