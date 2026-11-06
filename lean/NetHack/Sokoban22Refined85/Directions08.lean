import NetHack.Sokoban22Refined85.Directions07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir118_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 .north p = true := by
  change ((!walkGuard soko2_2.board support p 118 96 .north || decide (bonus 118 p ≤ bonus 96 p)) && ((PreciseRolling.stayTargets soko2_2.board 96 .north).all (fun landing => !pushGuard support p 118 96 74 landing || decide (bonus 118 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some landing)))) && (pushTargets soko2_2.board 96 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 118 96 74 landing || decide (bonus 118 p ≤ 1 - Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.hole landing + bonus 96 (change p 96 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check359 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check360 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir118_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 .south p = true := by
  rfl
theorem dir118_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 .east p = true := by
  change ((!walkGuard soko2_2.board support p 118 119 .east || decide (bonus 118 p ≤ bonus 119 p)) && ((PreciseRolling.stayTargets soko2_2.board 119 .east).all (fun landing => !pushGuard support p 118 119 120 landing || decide (bonus 118 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some landing)))) && (pushTargets soko2_2.board 119 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 118 119 120 landing || decide (bonus 118 p ≤ 1 - Generated.soko2_2Potential.boulder 119 - Generated.soko2_2Potential.hole landing + bonus 119 (change p 119 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check361 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check362 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir118_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 .west p = true := by
  rfl
theorem dir118_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 118 97 .northEast || decide (bonus 118 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check363 p, rfl⟩
theorem dir118_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 118 95 .northWest || decide (bonus 118 p ≤ bonus 95 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check364 p, rfl⟩
theorem dir118_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 118 141 .southEast || decide (bonus 118 p ≤ bonus 141 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check365 p, rfl⟩
theorem dir118_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 118 .southWest p = true := by
  rfl
theorem dir119_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 .north p = true := by
  change ((!walkGuard soko2_2.board support p 119 97 .north || decide (bonus 119 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check366 p, rfl⟩
theorem dir119_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 .south p = true := by
  change ((!walkGuard soko2_2.board support p 119 141 .south || decide (bonus 119 p ≤ bonus 141 p)) && ((PreciseRolling.stayTargets soko2_2.board 141 .south).all (fun landing => !pushGuard support p 119 141 163 landing || decide (bonus 119 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 141 + bonus 141 (change p 141 (some landing)))) && (pushTargets soko2_2.board 141 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 119 141 163 landing || decide (bonus 119 p ≤ 1 - Generated.soko2_2Potential.boulder 141 - Generated.soko2_2Potential.hole landing + bonus 141 (change p 141 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check367 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check368 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir119_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 .east p = true := by
  change ((!walkGuard soko2_2.board support p 119 120 .east || decide (bonus 119 p ≤ bonus 120 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check369 p, rfl⟩
theorem dir119_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 .west p = true := by
  change ((!walkGuard soko2_2.board support p 119 118 .west || decide (bonus 119 p ≤ bonus 118 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check370 p, rfl⟩
theorem dir119_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 119 98 .northEast || decide (bonus 119 p ≤ bonus 98 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check371 p, rfl⟩
theorem dir119_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 119 96 .northWest || decide (bonus 119 p ≤ bonus 96 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check372 p, rfl⟩
theorem dir119_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 .southEast p = true := by
  rfl
theorem dir119_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 119 .southWest p = true := by
  rfl
theorem dir120_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 .north p = true := by
  change ((!walkGuard soko2_2.board support p 120 98 .north || decide (bonus 120 p ≤ bonus 98 p)) && ((PreciseRolling.stayTargets soko2_2.board 98 .north).all (fun landing => !pushGuard support p 120 98 76 landing || decide (bonus 120 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 98 + bonus 98 (change p 98 (some landing)))) && (pushTargets soko2_2.board 98 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 120 98 76 landing || decide (bonus 120 p ≤ 1 - Generated.soko2_2Potential.boulder 98 - Generated.soko2_2Potential.hole landing + bonus 98 (change p 98 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check373 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check374 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir120_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 .south p = true := by
  rfl
theorem dir120_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 .east p = true := by
  rfl
theorem dir120_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 .west p = true := by
  change ((!walkGuard soko2_2.board support p 120 119 .west || decide (bonus 120 p ≤ bonus 119 p)) && ((PreciseRolling.stayTargets soko2_2.board 119 .west).all (fun landing => !pushGuard support p 120 119 118 landing || decide (bonus 120 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some landing)))) && (pushTargets soko2_2.board 119 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 120 119 118 landing || decide (bonus 120 p ≤ 1 - Generated.soko2_2Potential.boulder 119 - Generated.soko2_2Potential.hole landing + bonus 119 (change p 119 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check375 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check376 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir120_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 .northEast p = true := by
  rfl
theorem dir120_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 120 97 .northWest || decide (bonus 120 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check377 p, rfl⟩
theorem dir120_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 .southEast p = true := by
  rfl
theorem dir120_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 120 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 120 141 .southWest || decide (bonus 120 p ≤ bonus 141 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check378 p, rfl⟩
theorem dir122_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 .north p = true := by
  change ((!walkGuard soko2_2.board support p 122 100 .north || decide (bonus 122 p ≤ bonus 100 p)) && ((PreciseRolling.stayTargets soko2_2.board 100 .north).all (fun landing => !pushGuard support p 122 100 78 landing || decide (bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 100 + bonus 100 (change p 100 (some landing)))) && (pushTargets soko2_2.board 100 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 122 100 78 landing || decide (bonus 122 p ≤ 1 - Generated.soko2_2Potential.boulder 100 - Generated.soko2_2Potential.hole landing + bonus 100 (change p 100 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check379 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check380 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir122_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 .south p = true := by
  change ((!walkGuard soko2_2.board support p 122 144 .south || decide (bonus 122 p ≤ bonus 144 p)) && ((PreciseRolling.stayTargets soko2_2.board 144 .south).all (fun landing => !pushGuard support p 122 144 166 landing || decide (bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 144 + bonus 144 (change p 144 (some landing)))) && (pushTargets soko2_2.board 144 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 122 144 166 landing || decide (bonus 122 p ≤ 1 - Generated.soko2_2Potential.boulder 144 - Generated.soko2_2Potential.hole landing + bonus 144 (change p 144 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check381 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check382 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir122_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 .east p = true := by
  change ((!walkGuard soko2_2.board support p 122 123 .east || decide (bonus 122 p ≤ bonus 123 p)) && ((PreciseRolling.stayTargets soko2_2.board 123 .east).all (fun landing => !pushGuard support p 122 123 124 landing || decide (bonus 122 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some landing)))) && (pushTargets soko2_2.board 123 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 122 123 124 landing || decide (bonus 122 p ≤ 1 - Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.hole landing + bonus 123 (change p 123 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check383 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check384 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir122_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 .west p = true := by
  rfl
theorem dir122_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 122 101 .northEast || decide (bonus 122 p ≤ bonus 101 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check385 p, rfl⟩
theorem dir122_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 .northWest p = true := by
  rfl
theorem dir122_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 122 145 .southEast || decide (bonus 122 p ≤ bonus 145 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check386 p, rfl⟩
theorem dir122_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 122 .southWest p = true := by
  rfl
theorem dir123_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 .north p = true := by
  change ((!walkGuard soko2_2.board support p 123 101 .north || decide (bonus 123 p ≤ bonus 101 p)) && ((PreciseRolling.stayTargets soko2_2.board 101 .north).all (fun landing => !pushGuard support p 123 101 79 landing || decide (bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some landing)))) && (pushTargets soko2_2.board 101 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 123 101 79 landing || decide (bonus 123 p ≤ 1 - Generated.soko2_2Potential.boulder 101 - Generated.soko2_2Potential.hole landing + bonus 101 (change p 101 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check387 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check388 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir123_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 .south p = true := by
  change ((!walkGuard soko2_2.board support p 123 145 .south || decide (bonus 123 p ≤ bonus 145 p)) && ((PreciseRolling.stayTargets soko2_2.board 145 .south).all (fun landing => !pushGuard support p 123 145 167 landing || decide (bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some landing)))) && (pushTargets soko2_2.board 145 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 123 145 167 landing || decide (bonus 123 p ≤ 1 - Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.hole landing + bonus 145 (change p 145 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check389 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check390 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir123_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 .east p = true := by
  change ((!walkGuard soko2_2.board support p 123 124 .east || decide (bonus 123 p ≤ bonus 124 p)) && ((PreciseRolling.stayTargets soko2_2.board 124 .east).all (fun landing => !pushGuard support p 123 124 125 landing || decide (bonus 123 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some landing)))) && (pushTargets soko2_2.board 124 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 123 124 125 landing || decide (bonus 123 p ≤ 1 - Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.hole landing + bonus 124 (change p 124 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check391 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check392 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir123_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 .west p = true := by
  change ((!walkGuard soko2_2.board support p 123 122 .west || decide (bonus 123 p ≤ bonus 122 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check393 p, rfl⟩
theorem dir123_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 123 102 .northEast || decide (bonus 123 p ≤ bonus 102 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check394 p, rfl⟩
theorem dir123_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 123 100 .northWest || decide (bonus 123 p ≤ bonus 100 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check395 p, rfl⟩
theorem dir123_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 123 146 .southEast || decide (bonus 123 p ≤ bonus 146 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check396 p, rfl⟩
theorem dir123_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 123 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 123 144 .southWest || decide (bonus 123 p ≤ bonus 144 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check397 p, rfl⟩
theorem dir124_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 .north p = true := by
  change ((!walkGuard soko2_2.board support p 124 102 .north || decide (bonus 124 p ≤ bonus 102 p)) && ((PreciseRolling.stayTargets soko2_2.board 102 .north).all (fun landing => !pushGuard support p 124 102 80 landing || decide (bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some landing)))) && (pushTargets soko2_2.board 102 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 124 102 80 landing || decide (bonus 124 p ≤ 1 - Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.hole landing + bonus 102 (change p 102 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check398 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check399 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir124_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 .south p = true := by
  change ((!walkGuard soko2_2.board support p 124 146 .south || decide (bonus 124 p ≤ bonus 146 p)) && ((PreciseRolling.stayTargets soko2_2.board 146 .south).all (fun landing => !pushGuard support p 124 146 168 landing || decide (bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some landing)))) && (pushTargets soko2_2.board 146 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 124 146 168 landing || decide (bonus 124 p ≤ 1 - Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.hole landing + bonus 146 (change p 146 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check400 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check401 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir124_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 .east p = true := by
  change ((!walkGuard soko2_2.board support p 124 125 .east || decide (bonus 124 p ≤ bonus 125 p)) && ((PreciseRolling.stayTargets soko2_2.board 125 .east).all (fun landing => !pushGuard support p 124 125 126 landing || decide (bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some landing)))) && (pushTargets soko2_2.board 125 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 124 125 126 landing || decide (bonus 124 p ≤ 1 - Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.hole landing + bonus 125 (change p 125 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check402 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check403 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir124_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 .west p = true := by
  change ((!walkGuard soko2_2.board support p 124 123 .west || decide (bonus 124 p ≤ bonus 123 p)) && ((PreciseRolling.stayTargets soko2_2.board 123 .west).all (fun landing => !pushGuard support p 124 123 122 landing || decide (bonus 124 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some landing)))) && (pushTargets soko2_2.board 123 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 124 123 122 landing || decide (bonus 124 p ≤ 1 - Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.hole landing + bonus 123 (change p 123 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check404 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check405 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir124_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 124 103 .northEast || decide (bonus 124 p ≤ bonus 103 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check406 p, rfl⟩
theorem dir124_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 124 101 .northWest || decide (bonus 124 p ≤ bonus 101 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check407 p, rfl⟩
theorem dir124_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 124 147 .southEast || decide (bonus 124 p ≤ bonus 147 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check408 p, rfl⟩
theorem dir124_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 124 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 124 145 .southWest || decide (bonus 124 p ≤ bonus 145 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check409 p, rfl⟩
end NetHack.Sokoban22Refined85
