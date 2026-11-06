import NetHack.Sokoban32Refined.Directions06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir102_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 .north p = true := by
  change ((!walkGuard soko3_2.board support p 102 76 .north || decide (bonus 102 p ≤ bonus 76 p)) && ((PreciseRolling.stayTargets soko3_2.board 76 .north).all (fun landing => !pushGuard support p 102 76 50 landing || decide (bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 76 + bonus 76 (change p 76 (some landing)))) && (pushTargets soko3_2.board 76 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 102 76 50 landing || decide (bonus 102 p ≤ 1 - Generated.soko3_2Potential.boulder 76 - Generated.soko3_2Potential.hole landing + bonus 76 (change p 76 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check330 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check331 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir102_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 .south p = true := by
  change ((!walkGuard soko3_2.board support p 102 128 .south || decide (bonus 102 p ≤ bonus 128 p)) && ((PreciseRolling.stayTargets soko3_2.board 128 .south).all (fun landing => !pushGuard support p 102 128 154 landing || decide (bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 128 + bonus 128 (change p 128 (some landing)))) && (pushTargets soko3_2.board 128 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 102 128 154 landing || decide (bonus 102 p ≤ 1 - Generated.soko3_2Potential.boulder 128 - Generated.soko3_2Potential.hole landing + bonus 128 (change p 128 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check332 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check333 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir102_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 .east p = true := by
  rfl
theorem dir102_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 .west p = true := by
  change ((!walkGuard soko3_2.board support p 102 101 .west || decide (bonus 102 p ≤ bonus 101 p)) && ((PreciseRolling.stayTargets soko3_2.board 101 .west).all (fun landing => !pushGuard support p 102 101 100 landing || decide (bonus 102 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some landing)))) && (pushTargets soko3_2.board 101 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 102 101 100 landing || decide (bonus 102 p ≤ 1 - Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.hole landing + bonus 101 (change p 101 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check334 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check335 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir102_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 .northEast p = true := by
  rfl
theorem dir102_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 102 75 .northWest || decide (bonus 102 p ≤ bonus 75 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check336 p, rfl⟩
theorem dir102_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 .southEast p = true := by
  rfl
theorem dir102_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 102 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 102 127 .southWest || decide (bonus 102 p ≤ bonus 127 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check337 p, rfl⟩
theorem dir105_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 .north p = true := by
  change ((!walkGuard soko3_2.board support p 105 79 .north || decide (bonus 105 p ≤ bonus 79 p)) && ((PreciseRolling.stayTargets soko3_2.board 79 .north).all (fun landing => !pushGuard support p 105 79 53 landing || decide (bonus 105 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 79 + bonus 79 (change p 79 (some landing)))) && (pushTargets soko3_2.board 79 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 105 79 53 landing || decide (bonus 105 p ≤ 1 - Generated.soko3_2Potential.boulder 79 - Generated.soko3_2Potential.hole landing + bonus 79 (change p 79 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check338 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check339 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir105_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 .south p = true := by
  change ((!walkGuard soko3_2.board support p 105 131 .south || decide (bonus 105 p ≤ bonus 131 p)) && ((PreciseRolling.stayTargets soko3_2.board 131 .south).all (fun landing => !pushGuard support p 105 131 157 landing || decide (bonus 105 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 131 + bonus 131 (change p 131 (some landing)))) && (pushTargets soko3_2.board 131 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 105 131 157 landing || decide (bonus 105 p ≤ 1 - Generated.soko3_2Potential.boulder 131 - Generated.soko3_2Potential.hole landing + bonus 131 (change p 131 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check340 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check341 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir105_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 .east p = true := by
  change ((!walkGuard soko3_2.board support p 105 106 .east || decide (bonus 105 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check342 p, rfl⟩
theorem dir105_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 .west p = true := by
  rfl
theorem dir105_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 105 80 .northEast || decide (bonus 105 p ≤ bonus 80 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check343 p, rfl⟩
theorem dir105_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 .northWest p = true := by
  rfl
theorem dir105_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 105 132 .southEast || decide (bonus 105 p ≤ bonus 132 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check344 p, rfl⟩
theorem dir105_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 105 .southWest p = true := by
  rfl
theorem dir106_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 .north p = true := by
  change ((!walkGuard soko3_2.board support p 106 80 .north || decide (bonus 106 p ≤ bonus 80 p)) && ((PreciseRolling.stayTargets soko3_2.board 80 .north).all (fun landing => !pushGuard support p 106 80 54 landing || decide (bonus 106 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 80 + bonus 80 (change p 80 (some landing)))) && (pushTargets soko3_2.board 80 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 106 80 54 landing || decide (bonus 106 p ≤ 1 - Generated.soko3_2Potential.boulder 80 - Generated.soko3_2Potential.hole landing + bonus 80 (change p 80 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check345 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check346 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir106_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 .south p = true := by
  change ((!walkGuard soko3_2.board support p 106 132 .south || decide (bonus 106 p ≤ bonus 132 p)) && ((PreciseRolling.stayTargets soko3_2.board 132 .south).all (fun landing => !pushGuard support p 106 132 158 landing || decide (bonus 106 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some landing)))) && (pushTargets soko3_2.board 132 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 106 132 158 landing || decide (bonus 106 p ≤ 1 - Generated.soko3_2Potential.boulder 132 - Generated.soko3_2Potential.hole landing + bonus 132 (change p 132 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check347 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check348 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir106_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 .east p = true := by
  rfl
theorem dir106_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 .west p = true := by
  change ((!walkGuard soko3_2.board support p 106 105 .west || decide (bonus 106 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check349 p, rfl⟩
theorem dir106_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 .northEast p = true := by
  rfl
theorem dir106_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 106 79 .northWest || decide (bonus 106 p ≤ bonus 79 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check350 p, rfl⟩
theorem dir106_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 106 133 .southEast || decide (bonus 106 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check351 p, rfl⟩
theorem dir106_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 106 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 106 131 .southWest || decide (bonus 106 p ≤ bonus 131 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check352 p, rfl⟩
theorem dir108_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 .north p = true := by
  rfl
theorem dir108_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 .south p = true := by
  change ((!walkGuard soko3_2.board support p 108 134 .south || decide (bonus 108 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko3_2.board 134 .south).all (fun landing => !pushGuard support p 108 134 160 landing || decide (bonus 108 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko3_2.board 134 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 108 134 160 landing || decide (bonus 108 p ≤ 1 - Generated.soko3_2Potential.boulder 134 - Generated.soko3_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check353 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check354 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir108_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 .east p = true := by
  change ((!walkGuard soko3_2.board support p 108 109 .east || decide (bonus 108 p ≤ bonus 109 p)) && ((PreciseRolling.stayTargets soko3_2.board 109 .east).all (fun landing => !pushGuard support p 108 109 110 landing || decide (bonus 108 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 109 + bonus 109 (change p 109 (some landing)))) && (pushTargets soko3_2.board 109 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 108 109 110 landing || decide (bonus 108 p ≤ 1 - Generated.soko3_2Potential.boulder 109 - Generated.soko3_2Potential.hole landing + bonus 109 (change p 109 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check355 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check356 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir108_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 .west p = true := by
  rfl
theorem dir108_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 .northEast p = true := by
  rfl
theorem dir108_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 .northWest p = true := by
  rfl
theorem dir108_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 108 135 .southEast || decide (bonus 108 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check357 p, rfl⟩
theorem dir108_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 108 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 108 133 .southWest || decide (bonus 108 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check358 p, rfl⟩
theorem dir109_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 .north p = true := by
  rfl
theorem dir109_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 .south p = true := by
  change ((!walkGuard soko3_2.board support p 109 135 .south || decide (bonus 109 p ≤ bonus 135 p)) && ((PreciseRolling.stayTargets soko3_2.board 135 .south).all (fun landing => !pushGuard support p 109 135 161 landing || decide (bonus 109 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some landing)))) && (pushTargets soko3_2.board 135 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 109 135 161 landing || decide (bonus 109 p ≤ 1 - Generated.soko3_2Potential.boulder 135 - Generated.soko3_2Potential.hole landing + bonus 135 (change p 135 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check359 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check360 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir109_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 .east p = true := by
  change ((!walkGuard soko3_2.board support p 109 110 .east || decide (bonus 109 p ≤ bonus 110 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check361 p, rfl⟩
theorem dir109_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 .west p = true := by
  change ((!walkGuard soko3_2.board support p 109 108 .west || decide (bonus 109 p ≤ bonus 108 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check362 p, rfl⟩
theorem dir109_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 .northEast p = true := by
  rfl
theorem dir109_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 .northWest p = true := by
  rfl
theorem dir109_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 109 136 .southEast || decide (bonus 109 p ≤ bonus 136 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check363 p, rfl⟩
theorem dir109_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 109 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 109 134 .southWest || decide (bonus 109 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check364 p, rfl⟩
theorem dir110_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 .north p = true := by
  rfl
theorem dir110_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 .south p = true := by
  change ((!walkGuard soko3_2.board support p 110 136 .south || decide (bonus 110 p ≤ bonus 136 p)) && ((PreciseRolling.stayTargets soko3_2.board 136 .south).all (fun landing => !pushGuard support p 110 136 162 landing || decide (bonus 110 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some landing)))) && (pushTargets soko3_2.board 136 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 110 136 162 landing || decide (bonus 110 p ≤ 1 - Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.hole landing + bonus 136 (change p 136 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check365 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check366 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir110_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 .east p = true := by
  rfl
theorem dir110_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 .west p = true := by
  change ((!walkGuard soko3_2.board support p 110 109 .west || decide (bonus 110 p ≤ bonus 109 p)) && ((PreciseRolling.stayTargets soko3_2.board 109 .west).all (fun landing => !pushGuard support p 110 109 108 landing || decide (bonus 110 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 109 + bonus 109 (change p 109 (some landing)))) && (pushTargets soko3_2.board 109 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 110 109 108 landing || decide (bonus 110 p ≤ 1 - Generated.soko3_2Potential.boulder 109 - Generated.soko3_2Potential.hole landing + bonus 109 (change p 109 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check367 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check368 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir110_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 .northEast p = true := by
  rfl
theorem dir110_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 .northWest p = true := by
  rfl
theorem dir110_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 110 137 .southEast || decide (bonus 110 p ≤ bonus 137 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check369 p, rfl⟩
theorem dir110_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 110 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 110 135 .southWest || decide (bonus 110 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check370 p, rfl⟩
end NetHack.Sokoban32Refined
