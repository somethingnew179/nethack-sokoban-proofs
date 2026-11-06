import NetHack.Sokoban12CostPartition.Directions21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir334_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 .north p = true := by
  change ((!walkGuard soko1_2.board support p 334 308 .north || decide (bonus 334 p ≤ bonus 308 p)) && ((PreciseRolling.stayTargets soko1_2.board 308 .north).all (fun landing => !pushGuard support p 334 308 282 landing || decide (bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 308 + bonus 308 (change p 308 (some landing)))) && (pushTargets soko1_2.board 308 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 334 308 282 landing || decide (bonus 334 p ≤ 1 - Generated.soko1_2Potential.boulder 308 - Generated.soko1_2Potential.hole landing + bonus 308 (change p 308 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check969 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check970 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir334_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 .south p = true := by
  change ((!walkGuard soko1_2.board support p 334 360 .south || decide (bonus 334 p ≤ bonus 360 p)) && ((PreciseRolling.stayTargets soko1_2.board 360 .south).all (fun landing => !pushGuard support p 334 360 386 landing || decide (bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 360 + bonus 360 (change p 360 (some landing)))) && (pushTargets soko1_2.board 360 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 334 360 386 landing || decide (bonus 334 p ≤ 1 - Generated.soko1_2Potential.boulder 360 - Generated.soko1_2Potential.hole landing + bonus 360 (change p 360 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check971 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check972 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir334_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 .east p = true := by
  rfl
theorem dir334_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 .west p = true := by
  change ((!walkGuard soko1_2.board support p 334 333 .west || decide (bonus 334 p ≤ bonus 333 p)) && ((PreciseRolling.stayTargets soko1_2.board 333 .west).all (fun landing => !pushGuard support p 334 333 332 landing || decide (bonus 334 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some landing)))) && (pushTargets soko1_2.board 333 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 334 333 332 landing || decide (bonus 334 p ≤ 1 - Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.hole landing + bonus 333 (change p 333 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check973 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check974 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir334_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 .northEast p = true := by
  rfl
theorem dir334_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 334 307 .northWest || decide (bonus 334 p ≤ bonus 307 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check975 p, rfl⟩
theorem dir334_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 .southEast p = true := by
  rfl
theorem dir334_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 334 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 334 359 .southWest || decide (bonus 334 p ≤ bonus 359 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check976 p, rfl⟩
theorem dir336_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 .north p = true := by
  change ((!walkGuard soko1_2.board support p 336 310 .north || decide (bonus 336 p ≤ bonus 310 p)) && ((PreciseRolling.stayTargets soko1_2.board 310 .north).all (fun landing => !pushGuard support p 336 310 284 landing || decide (bonus 336 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 310 + bonus 310 (change p 310 (some landing)))) && (pushTargets soko1_2.board 310 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 336 310 284 landing || decide (bonus 336 p ≤ 1 - Generated.soko1_2Potential.boulder 310 - Generated.soko1_2Potential.hole landing + bonus 310 (change p 310 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check977 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check978 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir336_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 .south p = true := by
  rfl
theorem dir336_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 .east p = true := by
  rfl
theorem dir336_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 .west p = true := by
  rfl
theorem dir336_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 .northEast p = true := by
  rfl
theorem dir336_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 .northWest p = true := by
  rfl
theorem dir336_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 .southEast p = true := by
  rfl
theorem dir336_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 336 .southWest p = true := by
  rfl
theorem dir345_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 .north p = true := by
  change ((!walkGuard soko1_2.board support p 345 319 .north || decide (bonus 345 p ≤ bonus 319 p)) && ((PreciseRolling.stayTargets soko1_2.board 319 .north).all (fun landing => !pushGuard support p 345 319 293 landing || decide (bonus 345 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some landing)))) && (pushTargets soko1_2.board 319 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 345 319 293 landing || decide (bonus 345 p ≤ 1 - Generated.soko1_2Potential.boulder 319 - Generated.soko1_2Potential.hole landing + bonus 319 (change p 319 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check979 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check980 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir345_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 .south p = true := by
  change ((!walkGuard soko1_2.board support p 345 371 .south || decide (bonus 345 p ≤ bonus 371 p)) && ((PreciseRolling.stayTargets soko1_2.board 371 .south).all (fun landing => !pushGuard support p 345 371 397 landing || decide (bonus 345 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some landing)))) && (pushTargets soko1_2.board 371 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 345 371 397 landing || decide (bonus 345 p ≤ 1 - Generated.soko1_2Potential.boulder 371 - Generated.soko1_2Potential.hole landing + bonus 371 (change p 371 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check981 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check982 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir345_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 .east p = true := by
  rfl
theorem dir345_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 .west p = true := by
  rfl
theorem dir345_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 345 320 .northEast || decide (bonus 345 p ≤ bonus 320 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check983 p, rfl⟩
theorem dir345_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 345 318 .northWest || decide (bonus 345 p ≤ bonus 318 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check984 p, rfl⟩
theorem dir345_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 345 372 .southEast || decide (bonus 345 p ≤ bonus 372 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check985 p, rfl⟩
theorem dir345_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 345 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 345 370 .southWest || decide (bonus 345 p ≤ bonus 370 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check986 p, rfl⟩
theorem dir348_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 .north p = true := by
  change ((!walkGuard soko1_2.board support p 348 322 .north || decide (bonus 348 p ≤ bonus 322 p)) && ((PreciseRolling.stayTargets soko1_2.board 322 .north).all (fun landing => !pushGuard support p 348 322 296 landing || decide (bonus 348 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 322 + bonus 322 (change p 322 (some landing)))) && (pushTargets soko1_2.board 322 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 348 322 296 landing || decide (bonus 348 p ≤ 1 - Generated.soko1_2Potential.boulder 322 - Generated.soko1_2Potential.hole landing + bonus 322 (change p 322 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check987 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check988 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir348_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 .south p = true := by
  change ((!walkGuard soko1_2.board support p 348 374 .south || decide (bonus 348 p ≤ bonus 374 p)) && ((PreciseRolling.stayTargets soko1_2.board 374 .south).all (fun landing => !pushGuard support p 348 374 400 landing || decide (bonus 348 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 374 + bonus 374 (change p 374 (some landing)))) && (pushTargets soko1_2.board 374 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 348 374 400 landing || decide (bonus 348 p ≤ 1 - Generated.soko1_2Potential.boulder 374 - Generated.soko1_2Potential.hole landing + bonus 374 (change p 374 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check989 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check990 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir348_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 .east p = true := by
  rfl
theorem dir348_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 .west p = true := by
  rfl
theorem dir348_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 .northEast p = true := by
  rfl
theorem dir348_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 .northWest p = true := by
  rfl
theorem dir348_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 .southEast p = true := by
  rfl
theorem dir348_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 348 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 348 373 .southWest || decide (bonus 348 p ≤ bonus 373 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check991 p, rfl⟩
theorem dir356_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 .north p = true := by
  change ((!walkGuard soko1_2.board support p 356 330 .north || decide (bonus 356 p ≤ bonus 330 p)) && ((PreciseRolling.stayTargets soko1_2.board 330 .north).all (fun landing => !pushGuard support p 356 330 304 landing || decide (bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 330 + bonus 330 (change p 330 (some landing)))) && (pushTargets soko1_2.board 330 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 356 330 304 landing || decide (bonus 356 p ≤ 1 - Generated.soko1_2Potential.boulder 330 - Generated.soko1_2Potential.hole landing + bonus 330 (change p 330 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check992 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check993 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir356_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 .south p = true := by
  change ((!walkGuard soko1_2.board support p 356 382 .south || decide (bonus 356 p ≤ bonus 382 p)) && ((PreciseRolling.stayTargets soko1_2.board 382 .south).all (fun landing => !pushGuard support p 356 382 408 landing || decide (bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 382 + bonus 382 (change p 382 (some landing)))) && (pushTargets soko1_2.board 382 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 356 382 408 landing || decide (bonus 356 p ≤ 1 - Generated.soko1_2Potential.boulder 382 - Generated.soko1_2Potential.hole landing + bonus 382 (change p 382 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check994 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check995 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir356_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 .east p = true := by
  change ((!walkGuard soko1_2.board support p 356 357 .east || decide (bonus 356 p ≤ bonus 357 p)) && ((PreciseRolling.stayTargets soko1_2.board 357 .east).all (fun landing => !pushGuard support p 356 357 358 landing || decide (bonus 356 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some landing)))) && (pushTargets soko1_2.board 357 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 356 357 358 landing || decide (bonus 356 p ≤ 1 - Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.hole landing + bonus 357 (change p 357 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check996 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check997 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir356_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 .west p = true := by
  rfl
theorem dir356_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 356 331 .northEast || decide (bonus 356 p ≤ bonus 331 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check998 p, rfl⟩
theorem dir356_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 .northWest p = true := by
  rfl
theorem dir356_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 356 383 .southEast || decide (bonus 356 p ≤ bonus 383 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check999 p, rfl⟩
theorem dir356_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 356 .southWest p = true := by
  rfl
theorem dir357_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 .north p = true := by
  change ((!walkGuard soko1_2.board support p 357 331 .north || decide (bonus 357 p ≤ bonus 331 p)) && ((PreciseRolling.stayTargets soko1_2.board 331 .north).all (fun landing => !pushGuard support p 357 331 305 landing || decide (bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some landing)))) && (pushTargets soko1_2.board 331 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 357 331 305 landing || decide (bonus 357 p ≤ 1 - Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.hole landing + bonus 331 (change p 331 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1000 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1001 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir357_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 .south p = true := by
  change ((!walkGuard soko1_2.board support p 357 383 .south || decide (bonus 357 p ≤ bonus 383 p)) && ((PreciseRolling.stayTargets soko1_2.board 383 .south).all (fun landing => !pushGuard support p 357 383 409 landing || decide (bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some landing)))) && (pushTargets soko1_2.board 383 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 357 383 409 landing || decide (bonus 357 p ≤ 1 - Generated.soko1_2Potential.boulder 383 - Generated.soko1_2Potential.hole landing + bonus 383 (change p 383 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1002 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1003 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir357_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 .east p = true := by
  change ((!walkGuard soko1_2.board support p 357 358 .east || decide (bonus 357 p ≤ bonus 358 p)) && ((PreciseRolling.stayTargets soko1_2.board 358 .east).all (fun landing => !pushGuard support p 357 358 359 landing || decide (bonus 357 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some landing)))) && (pushTargets soko1_2.board 358 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 357 358 359 landing || decide (bonus 357 p ≤ 1 - Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.hole landing + bonus 358 (change p 358 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1004 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1005 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir357_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 .west p = true := by
  change ((!walkGuard soko1_2.board support p 357 356 .west || decide (bonus 357 p ≤ bonus 356 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1006 p, rfl⟩
theorem dir357_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 357 332 .northEast || decide (bonus 357 p ≤ bonus 332 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1007 p, rfl⟩
theorem dir357_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 357 330 .northWest || decide (bonus 357 p ≤ bonus 330 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1008 p, rfl⟩
theorem dir357_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 357 384 .southEast || decide (bonus 357 p ≤ bonus 384 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1009 p, rfl⟩
theorem dir357_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 357 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 357 382 .southWest || decide (bonus 357 p ≤ bonus 382 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1010 p, rfl⟩
end NetHack.Sokoban12CostPartition
