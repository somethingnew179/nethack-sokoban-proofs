import NetHack.Sokoban12CostPartition.Directions20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir322_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 .north p = true := by
  change ((!walkGuard soko1_2.board support p 322 296 .north || decide (bonus 322 p ≤ bonus 296 p)) && ((PreciseRolling.stayTargets soko1_2.board 296 .north).all (fun landing => !pushGuard support p 322 296 270 landing || decide (bonus 322 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 296 + bonus 296 (change p 296 (some landing)))) && (pushTargets soko1_2.board 296 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 322 296 270 landing || decide (bonus 322 p ≤ 1 - Generated.soko1_2Potential.boulder 296 - Generated.soko1_2Potential.hole landing + bonus 296 (change p 296 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check922 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check923 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir322_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 .south p = true := by
  change ((!walkGuard soko1_2.board support p 322 348 .south || decide (bonus 322 p ≤ bonus 348 p)) && ((PreciseRolling.stayTargets soko1_2.board 348 .south).all (fun landing => !pushGuard support p 322 348 374 landing || decide (bonus 322 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 348 + bonus 348 (change p 348 (some landing)))) && (pushTargets soko1_2.board 348 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 322 348 374 landing || decide (bonus 322 p ≤ 1 - Generated.soko1_2Potential.boulder 348 - Generated.soko1_2Potential.hole landing + bonus 348 (change p 348 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check924 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check925 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir322_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 .east p = true := by
  rfl
theorem dir322_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 .west p = true := by
  rfl
theorem dir322_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 322 297 .northEast || decide (bonus 322 p ≤ bonus 297 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check926 p, rfl⟩
theorem dir322_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 .northWest p = true := by
  rfl
theorem dir322_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 .southEast p = true := by
  rfl
theorem dir322_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 322 .southWest p = true := by
  rfl
theorem dir328_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 .north p = true := by
  rfl
theorem dir328_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 .south p = true := by
  rfl
theorem dir328_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 .east p = true := by
  rfl
theorem dir328_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 .west p = true := by
  rfl
theorem dir328_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 .northEast p = true := by
  rfl
theorem dir328_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 .northWest p = true := by
  rfl
theorem dir328_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 .southEast p = true := by
  rfl
theorem dir328_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 328 .southWest p = true := by
  rfl
theorem dir330_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 .north p = true := by
  change ((!walkGuard soko1_2.board support p 330 304 .north || decide (bonus 330 p ≤ bonus 304 p)) && ((PreciseRolling.stayTargets soko1_2.board 304 .north).all (fun landing => !pushGuard support p 330 304 278 landing || decide (bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 304 + bonus 304 (change p 304 (some landing)))) && (pushTargets soko1_2.board 304 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 330 304 278 landing || decide (bonus 330 p ≤ 1 - Generated.soko1_2Potential.boulder 304 - Generated.soko1_2Potential.hole landing + bonus 304 (change p 304 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check927 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check928 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir330_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 .south p = true := by
  change ((!walkGuard soko1_2.board support p 330 356 .south || decide (bonus 330 p ≤ bonus 356 p)) && ((PreciseRolling.stayTargets soko1_2.board 356 .south).all (fun landing => !pushGuard support p 330 356 382 landing || decide (bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 356 + bonus 356 (change p 356 (some landing)))) && (pushTargets soko1_2.board 356 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 330 356 382 landing || decide (bonus 330 p ≤ 1 - Generated.soko1_2Potential.boulder 356 - Generated.soko1_2Potential.hole landing + bonus 356 (change p 356 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check929 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check930 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir330_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 .east p = true := by
  change ((!walkGuard soko1_2.board support p 330 331 .east || decide (bonus 330 p ≤ bonus 331 p)) && ((PreciseRolling.stayTargets soko1_2.board 331 .east).all (fun landing => !pushGuard support p 330 331 332 landing || decide (bonus 330 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some landing)))) && (pushTargets soko1_2.board 331 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 330 331 332 landing || decide (bonus 330 p ≤ 1 - Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.hole landing + bonus 331 (change p 331 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check931 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check932 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir330_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 .west p = true := by
  rfl
theorem dir330_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 330 305 .northEast || decide (bonus 330 p ≤ bonus 305 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check933 p, rfl⟩
theorem dir330_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 .northWest p = true := by
  rfl
theorem dir330_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 330 357 .southEast || decide (bonus 330 p ≤ bonus 357 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check934 p, rfl⟩
theorem dir330_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 330 .southWest p = true := by
  rfl
theorem dir331_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 .north p = true := by
  change ((!walkGuard soko1_2.board support p 331 305 .north || decide (bonus 331 p ≤ bonus 305 p)) && ((PreciseRolling.stayTargets soko1_2.board 305 .north).all (fun landing => !pushGuard support p 331 305 279 landing || decide (bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some landing)))) && (pushTargets soko1_2.board 305 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 331 305 279 landing || decide (bonus 331 p ≤ 1 - Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.hole landing + bonus 305 (change p 305 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check935 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check936 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir331_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 .south p = true := by
  change ((!walkGuard soko1_2.board support p 331 357 .south || decide (bonus 331 p ≤ bonus 357 p)) && ((PreciseRolling.stayTargets soko1_2.board 357 .south).all (fun landing => !pushGuard support p 331 357 383 landing || decide (bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some landing)))) && (pushTargets soko1_2.board 357 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 331 357 383 landing || decide (bonus 331 p ≤ 1 - Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.hole landing + bonus 357 (change p 357 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check937 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check938 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir331_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 .east p = true := by
  change ((!walkGuard soko1_2.board support p 331 332 .east || decide (bonus 331 p ≤ bonus 332 p)) && ((PreciseRolling.stayTargets soko1_2.board 332 .east).all (fun landing => !pushGuard support p 331 332 333 landing || decide (bonus 331 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some landing)))) && (pushTargets soko1_2.board 332 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 331 332 333 landing || decide (bonus 331 p ≤ 1 - Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.hole landing + bonus 332 (change p 332 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check939 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check940 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir331_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 .west p = true := by
  change ((!walkGuard soko1_2.board support p 331 330 .west || decide (bonus 331 p ≤ bonus 330 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check941 p, rfl⟩
theorem dir331_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 331 306 .northEast || decide (bonus 331 p ≤ bonus 306 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check942 p, rfl⟩
theorem dir331_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 331 304 .northWest || decide (bonus 331 p ≤ bonus 304 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check943 p, rfl⟩
theorem dir331_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 331 358 .southEast || decide (bonus 331 p ≤ bonus 358 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check944 p, rfl⟩
theorem dir331_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 331 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 331 356 .southWest || decide (bonus 331 p ≤ bonus 356 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check945 p, rfl⟩
theorem dir332_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 .north p = true := by
  change ((!walkGuard soko1_2.board support p 332 306 .north || decide (bonus 332 p ≤ bonus 306 p)) && ((PreciseRolling.stayTargets soko1_2.board 306 .north).all (fun landing => !pushGuard support p 332 306 280 landing || decide (bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some landing)))) && (pushTargets soko1_2.board 306 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 332 306 280 landing || decide (bonus 332 p ≤ 1 - Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.hole landing + bonus 306 (change p 306 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check946 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check947 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir332_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 .south p = true := by
  change ((!walkGuard soko1_2.board support p 332 358 .south || decide (bonus 332 p ≤ bonus 358 p)) && ((PreciseRolling.stayTargets soko1_2.board 358 .south).all (fun landing => !pushGuard support p 332 358 384 landing || decide (bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some landing)))) && (pushTargets soko1_2.board 358 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 332 358 384 landing || decide (bonus 332 p ≤ 1 - Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.hole landing + bonus 358 (change p 358 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check948 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check949 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir332_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 .east p = true := by
  change ((!walkGuard soko1_2.board support p 332 333 .east || decide (bonus 332 p ≤ bonus 333 p)) && ((PreciseRolling.stayTargets soko1_2.board 333 .east).all (fun landing => !pushGuard support p 332 333 334 landing || decide (bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some landing)))) && (pushTargets soko1_2.board 333 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 332 333 334 landing || decide (bonus 332 p ≤ 1 - Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.hole landing + bonus 333 (change p 333 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check950 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check951 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir332_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 .west p = true := by
  change ((!walkGuard soko1_2.board support p 332 331 .west || decide (bonus 332 p ≤ bonus 331 p)) && ((PreciseRolling.stayTargets soko1_2.board 331 .west).all (fun landing => !pushGuard support p 332 331 330 landing || decide (bonus 332 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some landing)))) && (pushTargets soko1_2.board 331 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 332 331 330 landing || decide (bonus 332 p ≤ 1 - Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.hole landing + bonus 331 (change p 331 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check952 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check953 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir332_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 332 307 .northEast || decide (bonus 332 p ≤ bonus 307 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check954 p, rfl⟩
theorem dir332_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 332 305 .northWest || decide (bonus 332 p ≤ bonus 305 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check955 p, rfl⟩
theorem dir332_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 332 359 .southEast || decide (bonus 332 p ≤ bonus 359 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check956 p, rfl⟩
theorem dir332_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 332 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 332 357 .southWest || decide (bonus 332 p ≤ bonus 357 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check957 p, rfl⟩
theorem dir333_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 .north p = true := by
  change ((!walkGuard soko1_2.board support p 333 307 .north || decide (bonus 333 p ≤ bonus 307 p)) && ((PreciseRolling.stayTargets soko1_2.board 307 .north).all (fun landing => !pushGuard support p 333 307 281 landing || decide (bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some landing)))) && (pushTargets soko1_2.board 307 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 333 307 281 landing || decide (bonus 333 p ≤ 1 - Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.hole landing + bonus 307 (change p 307 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check958 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check959 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir333_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 .south p = true := by
  change ((!walkGuard soko1_2.board support p 333 359 .south || decide (bonus 333 p ≤ bonus 359 p)) && ((PreciseRolling.stayTargets soko1_2.board 359 .south).all (fun landing => !pushGuard support p 333 359 385 landing || decide (bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some landing)))) && (pushTargets soko1_2.board 359 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 333 359 385 landing || decide (bonus 333 p ≤ 1 - Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.hole landing + bonus 359 (change p 359 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check960 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check961 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir333_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 .east p = true := by
  change ((!walkGuard soko1_2.board support p 333 334 .east || decide (bonus 333 p ≤ bonus 334 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check962 p, rfl⟩
theorem dir333_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 .west p = true := by
  change ((!walkGuard soko1_2.board support p 333 332 .west || decide (bonus 333 p ≤ bonus 332 p)) && ((PreciseRolling.stayTargets soko1_2.board 332 .west).all (fun landing => !pushGuard support p 333 332 331 landing || decide (bonus 333 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some landing)))) && (pushTargets soko1_2.board 332 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 333 332 331 landing || decide (bonus 333 p ≤ 1 - Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.hole landing + bonus 332 (change p 332 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check963 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check964 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir333_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 333 308 .northEast || decide (bonus 333 p ≤ bonus 308 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check965 p, rfl⟩
theorem dir333_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 333 306 .northWest || decide (bonus 333 p ≤ bonus 306 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check966 p, rfl⟩
theorem dir333_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 333 360 .southEast || decide (bonus 333 p ≤ bonus 360 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check967 p, rfl⟩
theorem dir333_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 333 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 333 358 .southWest || decide (bonus 333 p ≤ bonus 358 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check968 p, rfl⟩
end NetHack.Sokoban12CostPartition
