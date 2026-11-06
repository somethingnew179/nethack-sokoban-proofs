import NetHack.Sokoban22Refined85.Directions06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir106_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 .north p = true := by
  change ((!walkGuard soko2_2.board support p 106 84 .north || decide (bonus 106 p ≤ bonus 84 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check314 p, rfl⟩
theorem dir106_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 .south p = true := by
  change ((!walkGuard soko2_2.board support p 106 128 .south || decide (bonus 106 p ≤ bonus 128 p)) && ((PreciseRolling.stayTargets soko2_2.board 128 .south).all (fun landing => !pushGuard support p 106 128 150 landing || decide (bonus 106 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 128 + bonus 128 (change p 128 (some landing)))) && (pushTargets soko2_2.board 128 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 106 128 150 landing || decide (bonus 106 p ≤ 1 - Generated.soko2_2Potential.boulder 128 - Generated.soko2_2Potential.hole landing + bonus 128 (change p 128 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check315 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check316 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir106_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 .east p = true := by
  rfl
theorem dir106_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 .west p = true := by
  change ((!walkGuard soko2_2.board support p 106 105 .west || decide (bonus 106 p ≤ bonus 105 p)) && ((PreciseRolling.stayTargets soko2_2.board 105 .west).all (fun landing => !pushGuard support p 106 105 104 landing || decide (bonus 106 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some landing)))) && (pushTargets soko2_2.board 105 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 106 105 104 landing || decide (bonus 106 p ≤ 1 - Generated.soko2_2Potential.boulder 105 - Generated.soko2_2Potential.hole landing + bonus 105 (change p 105 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check317 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check318 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir106_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 .northEast p = true := by
  rfl
theorem dir106_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 106 83 .northWest || decide (bonus 106 p ≤ bonus 83 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check319 p, rfl⟩
theorem dir106_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 .southEast p = true := by
  rfl
theorem dir106_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 106 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 106 127 .southWest || decide (bonus 106 p ≤ bonus 127 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check320 p, rfl⟩
theorem dir111_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 .north p = true := by
  change ((!walkGuard soko2_2.board support p 111 89 .north || decide (bonus 111 p ≤ bonus 89 p)) && ((PreciseRolling.stayTargets soko2_2.board 89 .north).all (fun landing => !pushGuard support p 111 89 67 landing || decide (bonus 111 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 89 + bonus 89 (change p 89 (some landing)))) && (pushTargets soko2_2.board 89 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 111 89 67 landing || decide (bonus 111 p ≤ 1 - Generated.soko2_2Potential.boulder 89 - Generated.soko2_2Potential.hole landing + bonus 89 (change p 89 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check321 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check322 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir111_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 .south p = true := by
  change ((!walkGuard soko2_2.board support p 111 133 .south || decide (bonus 111 p ≤ bonus 133 p)) && ((PreciseRolling.stayTargets soko2_2.board 133 .south).all (fun landing => !pushGuard support p 111 133 155 landing || decide (bonus 111 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 133 + bonus 133 (change p 133 (some landing)))) && (pushTargets soko2_2.board 133 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 111 133 155 landing || decide (bonus 111 p ≤ 1 - Generated.soko2_2Potential.boulder 133 - Generated.soko2_2Potential.hole landing + bonus 133 (change p 133 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check323 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check324 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir111_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 .east p = true := by
  rfl
theorem dir111_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 .west p = true := by
  rfl
theorem dir111_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 111 90 .northEast || decide (bonus 111 p ≤ bonus 90 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check325 p, rfl⟩
theorem dir111_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 .northWest p = true := by
  rfl
theorem dir111_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 111 134 .southEast || decide (bonus 111 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check326 p, rfl⟩
theorem dir111_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 111 .southWest p = true := by
  rfl
theorem dir113_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 .north p = true := by
  change ((!walkGuard soko2_2.board support p 113 91 .north || decide (bonus 113 p ≤ bonus 91 p)) && ((PreciseRolling.stayTargets soko2_2.board 91 .north).all (fun landing => !pushGuard support p 113 91 69 landing || decide (bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 91 + bonus 91 (change p 91 (some landing)))) && (pushTargets soko2_2.board 91 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 113 91 69 landing || decide (bonus 113 p ≤ 1 - Generated.soko2_2Potential.boulder 91 - Generated.soko2_2Potential.hole landing + bonus 91 (change p 91 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check327 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check328 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir113_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 .south p = true := by
  change ((!walkGuard soko2_2.board support p 113 135 .south || decide (bonus 113 p ≤ bonus 135 p)) && ((PreciseRolling.stayTargets soko2_2.board 135 .south).all (fun landing => !pushGuard support p 113 135 157 landing || decide (bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some landing)))) && (pushTargets soko2_2.board 135 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 113 135 157 landing || decide (bonus 113 p ≤ 1 - Generated.soko2_2Potential.boulder 135 - Generated.soko2_2Potential.hole landing + bonus 135 (change p 135 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check329 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check330 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir113_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 .east p = true := by
  change ((!walkGuard soko2_2.board support p 113 114 .east || decide (bonus 113 p ≤ bonus 114 p)) && ((PreciseRolling.stayTargets soko2_2.board 114 .east).all (fun landing => !pushGuard support p 113 114 115 landing || decide (bonus 113 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 114 + bonus 114 (change p 114 (some landing)))) && (pushTargets soko2_2.board 114 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 113 114 115 landing || decide (bonus 113 p ≤ 1 - Generated.soko2_2Potential.boulder 114 - Generated.soko2_2Potential.hole landing + bonus 114 (change p 114 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check331 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check332 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir113_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 .west p = true := by
  rfl
theorem dir113_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 .northEast p = true := by
  rfl
theorem dir113_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 113 90 .northWest || decide (bonus 113 p ≤ bonus 90 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check333 p, rfl⟩
theorem dir113_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 113 136 .southEast || decide (bonus 113 p ≤ bonus 136 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check334 p, rfl⟩
theorem dir113_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 113 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 113 134 .southWest || decide (bonus 113 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check335 p, rfl⟩
theorem dir114_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 .north p = true := by
  rfl
theorem dir114_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 .south p = true := by
  change ((!walkGuard soko2_2.board support p 114 136 .south || decide (bonus 114 p ≤ bonus 136 p)) && ((PreciseRolling.stayTargets soko2_2.board 136 .south).all (fun landing => !pushGuard support p 114 136 158 landing || decide (bonus 114 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 136 + bonus 136 (change p 136 (some landing)))) && (pushTargets soko2_2.board 136 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 114 136 158 landing || decide (bonus 114 p ≤ 1 - Generated.soko2_2Potential.boulder 136 - Generated.soko2_2Potential.hole landing + bonus 136 (change p 136 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check336 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check337 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir114_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 .east p = true := by
  change ((!walkGuard soko2_2.board support p 114 115 .east || decide (bonus 114 p ≤ bonus 115 p)) && ((PreciseRolling.stayTargets soko2_2.board 115 .east).all (fun landing => !pushGuard support p 114 115 116 landing || decide (bonus 114 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 115 + bonus 115 (change p 115 (some landing)))) && (pushTargets soko2_2.board 115 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 114 115 116 landing || decide (bonus 114 p ≤ 1 - Generated.soko2_2Potential.boulder 115 - Generated.soko2_2Potential.hole landing + bonus 115 (change p 115 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check338 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check339 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir114_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 .west p = true := by
  change ((!walkGuard soko2_2.board support p 114 113 .west || decide (bonus 114 p ≤ bonus 113 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check340 p, rfl⟩
theorem dir114_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 114 93 .northEast || decide (bonus 114 p ≤ bonus 93 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check341 p, rfl⟩
theorem dir114_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 114 91 .northWest || decide (bonus 114 p ≤ bonus 91 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check342 p, rfl⟩
theorem dir114_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 .southEast p = true := by
  rfl
theorem dir114_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 114 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 114 135 .southWest || decide (bonus 114 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check343 p, rfl⟩
theorem dir115_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 .north p = true := by
  change ((!walkGuard soko2_2.board support p 115 93 .north || decide (bonus 115 p ≤ bonus 93 p)) && ((PreciseRolling.stayTargets soko2_2.board 93 .north).all (fun landing => !pushGuard support p 115 93 71 landing || decide (bonus 115 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 93 + bonus 93 (change p 93 (some landing)))) && (pushTargets soko2_2.board 93 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 115 93 71 landing || decide (bonus 115 p ≤ 1 - Generated.soko2_2Potential.boulder 93 - Generated.soko2_2Potential.hole landing + bonus 93 (change p 93 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check344 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check345 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir115_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 .south p = true := by
  rfl
theorem dir115_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 .east p = true := by
  change ((!walkGuard soko2_2.board support p 115 116 .east || decide (bonus 115 p ≤ bonus 116 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check346 p, rfl⟩
theorem dir115_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 .west p = true := by
  change ((!walkGuard soko2_2.board support p 115 114 .west || decide (bonus 115 p ≤ bonus 114 p)) && ((PreciseRolling.stayTargets soko2_2.board 114 .west).all (fun landing => !pushGuard support p 115 114 113 landing || decide (bonus 115 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 114 + bonus 114 (change p 114 (some landing)))) && (pushTargets soko2_2.board 114 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 115 114 113 landing || decide (bonus 115 p ≤ 1 - Generated.soko2_2Potential.boulder 114 - Generated.soko2_2Potential.hole landing + bonus 114 (change p 114 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check347 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check348 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir115_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 115 94 .northEast || decide (bonus 115 p ≤ bonus 94 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check349 p, rfl⟩
theorem dir115_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 .northWest p = true := by
  rfl
theorem dir115_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 115 138 .southEast || decide (bonus 115 p ≤ bonus 138 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check350 p, rfl⟩
theorem dir115_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 115 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 115 136 .southWest || decide (bonus 115 p ≤ bonus 136 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check351 p, rfl⟩
theorem dir116_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 .north p = true := by
  change ((!walkGuard soko2_2.board support p 116 94 .north || decide (bonus 116 p ≤ bonus 94 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check352 p, rfl⟩
theorem dir116_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 .south p = true := by
  change ((!walkGuard soko2_2.board support p 116 138 .south || decide (bonus 116 p ≤ bonus 138 p)) && ((PreciseRolling.stayTargets soko2_2.board 138 .south).all (fun landing => !pushGuard support p 116 138 160 landing || decide (bonus 116 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 138 + bonus 138 (change p 138 (some landing)))) && (pushTargets soko2_2.board 138 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 116 138 160 landing || decide (bonus 116 p ≤ 1 - Generated.soko2_2Potential.boulder 138 - Generated.soko2_2Potential.hole landing + bonus 138 (change p 138 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check353 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check354 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir116_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 .east p = true := by
  rfl
theorem dir116_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 .west p = true := by
  change ((!walkGuard soko2_2.board support p 116 115 .west || decide (bonus 116 p ≤ bonus 115 p)) && ((PreciseRolling.stayTargets soko2_2.board 115 .west).all (fun landing => !pushGuard support p 116 115 114 landing || decide (bonus 116 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 115 + bonus 115 (change p 115 (some landing)))) && (pushTargets soko2_2.board 115 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 116 115 114 landing || decide (bonus 116 p ≤ 1 - Generated.soko2_2Potential.boulder 115 - Generated.soko2_2Potential.hole landing + bonus 115 (change p 115 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check355 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check356 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir116_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 116 95 .northEast || decide (bonus 116 p ≤ bonus 95 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check357 p, rfl⟩
theorem dir116_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 116 93 .northWest || decide (bonus 116 p ≤ bonus 93 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check358 p, rfl⟩
theorem dir116_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 .southEast p = true := by
  rfl
theorem dir116_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 116 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
