import NetHack.Sokoban12CostPartition.Directions22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir358_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 .north p = true := by
  change ((!walkGuard soko1_2.board support p 358 332 .north || decide (bonus 358 p ≤ bonus 332 p)) && ((PreciseRolling.stayTargets soko1_2.board 332 .north).all (fun landing => !pushGuard support p 358 332 306 landing || decide (bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some landing)))) && (pushTargets soko1_2.board 332 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 358 332 306 landing || decide (bonus 358 p ≤ 1 - Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.hole landing + bonus 332 (change p 332 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1011 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1012 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir358_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 .south p = true := by
  change ((!walkGuard soko1_2.board support p 358 384 .south || decide (bonus 358 p ≤ bonus 384 p)) && ((PreciseRolling.stayTargets soko1_2.board 384 .south).all (fun landing => !pushGuard support p 358 384 410 landing || decide (bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some landing)))) && (pushTargets soko1_2.board 384 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 358 384 410 landing || decide (bonus 358 p ≤ 1 - Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.hole landing + bonus 384 (change p 384 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1013 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1014 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir358_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 .east p = true := by
  change ((!walkGuard soko1_2.board support p 358 359 .east || decide (bonus 358 p ≤ bonus 359 p)) && ((PreciseRolling.stayTargets soko1_2.board 359 .east).all (fun landing => !pushGuard support p 358 359 360 landing || decide (bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some landing)))) && (pushTargets soko1_2.board 359 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 358 359 360 landing || decide (bonus 358 p ≤ 1 - Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.hole landing + bonus 359 (change p 359 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1015 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1016 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir358_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 .west p = true := by
  change ((!walkGuard soko1_2.board support p 358 357 .west || decide (bonus 358 p ≤ bonus 357 p)) && ((PreciseRolling.stayTargets soko1_2.board 357 .west).all (fun landing => !pushGuard support p 358 357 356 landing || decide (bonus 358 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some landing)))) && (pushTargets soko1_2.board 357 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 358 357 356 landing || decide (bonus 358 p ≤ 1 - Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.hole landing + bonus 357 (change p 357 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1017 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1018 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir358_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 358 333 .northEast || decide (bonus 358 p ≤ bonus 333 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1019 p, rfl⟩
theorem dir358_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 358 331 .northWest || decide (bonus 358 p ≤ bonus 331 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1020 p, rfl⟩
theorem dir358_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 358 385 .southEast || decide (bonus 358 p ≤ bonus 385 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1021 p, rfl⟩
theorem dir358_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 358 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 358 383 .southWest || decide (bonus 358 p ≤ bonus 383 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1022 p, rfl⟩
theorem dir359_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 .north p = true := by
  change ((!walkGuard soko1_2.board support p 359 333 .north || decide (bonus 359 p ≤ bonus 333 p)) && ((PreciseRolling.stayTargets soko1_2.board 333 .north).all (fun landing => !pushGuard support p 359 333 307 landing || decide (bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some landing)))) && (pushTargets soko1_2.board 333 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 359 333 307 landing || decide (bonus 359 p ≤ 1 - Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.hole landing + bonus 333 (change p 333 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1023 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1024 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir359_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 .south p = true := by
  change ((!walkGuard soko1_2.board support p 359 385 .south || decide (bonus 359 p ≤ bonus 385 p)) && ((PreciseRolling.stayTargets soko1_2.board 385 .south).all (fun landing => !pushGuard support p 359 385 411 landing || decide (bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some landing)))) && (pushTargets soko1_2.board 385 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 359 385 411 landing || decide (bonus 359 p ≤ 1 - Generated.soko1_2Potential.boulder 385 - Generated.soko1_2Potential.hole landing + bonus 385 (change p 385 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1025 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1026 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir359_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 .east p = true := by
  change ((!walkGuard soko1_2.board support p 359 360 .east || decide (bonus 359 p ≤ bonus 360 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1027 p, rfl⟩
theorem dir359_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 .west p = true := by
  change ((!walkGuard soko1_2.board support p 359 358 .west || decide (bonus 359 p ≤ bonus 358 p)) && ((PreciseRolling.stayTargets soko1_2.board 358 .west).all (fun landing => !pushGuard support p 359 358 357 landing || decide (bonus 359 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some landing)))) && (pushTargets soko1_2.board 358 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 359 358 357 landing || decide (bonus 359 p ≤ 1 - Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.hole landing + bonus 358 (change p 358 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1028 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1029 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir359_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 359 334 .northEast || decide (bonus 359 p ≤ bonus 334 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1030 p, rfl⟩
theorem dir359_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 359 332 .northWest || decide (bonus 359 p ≤ bonus 332 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1031 p, rfl⟩
theorem dir359_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 359 386 .southEast || decide (bonus 359 p ≤ bonus 386 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1032 p, rfl⟩
theorem dir359_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 359 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 359 384 .southWest || decide (bonus 359 p ≤ bonus 384 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1033 p, rfl⟩
theorem dir360_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 .north p = true := by
  change ((!walkGuard soko1_2.board support p 360 334 .north || decide (bonus 360 p ≤ bonus 334 p)) && ((PreciseRolling.stayTargets soko1_2.board 334 .north).all (fun landing => !pushGuard support p 360 334 308 landing || decide (bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 334 + bonus 334 (change p 334 (some landing)))) && (pushTargets soko1_2.board 334 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 360 334 308 landing || decide (bonus 360 p ≤ 1 - Generated.soko1_2Potential.boulder 334 - Generated.soko1_2Potential.hole landing + bonus 334 (change p 334 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1034 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1035 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir360_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 .south p = true := by
  change ((!walkGuard soko1_2.board support p 360 386 .south || decide (bonus 360 p ≤ bonus 386 p)) && ((PreciseRolling.stayTargets soko1_2.board 386 .south).all (fun landing => !pushGuard support p 360 386 412 landing || decide (bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 386 + bonus 386 (change p 386 (some landing)))) && (pushTargets soko1_2.board 386 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 360 386 412 landing || decide (bonus 360 p ≤ 1 - Generated.soko1_2Potential.boulder 386 - Generated.soko1_2Potential.hole landing + bonus 386 (change p 386 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1036 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1037 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir360_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 .east p = true := by
  rfl
theorem dir360_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 .west p = true := by
  change ((!walkGuard soko1_2.board support p 360 359 .west || decide (bonus 360 p ≤ bonus 359 p)) && ((PreciseRolling.stayTargets soko1_2.board 359 .west).all (fun landing => !pushGuard support p 360 359 358 landing || decide (bonus 360 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some landing)))) && (pushTargets soko1_2.board 359 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 360 359 358 landing || decide (bonus 360 p ≤ 1 - Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.hole landing + bonus 359 (change p 359 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1038 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1039 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir360_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 .northEast p = true := by
  rfl
theorem dir360_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 360 333 .northWest || decide (bonus 360 p ≤ bonus 333 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1040 p, rfl⟩
theorem dir360_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 .southEast p = true := by
  rfl
theorem dir360_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 360 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 360 385 .southWest || decide (bonus 360 p ≤ bonus 385 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1041 p, rfl⟩
theorem dir370_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 .north p = true := by
  rfl
theorem dir370_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 .south p = true := by
  change ((!walkGuard soko1_2.board support p 370 396 .south || decide (bonus 370 p ≤ bonus 396 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1042 p, rfl⟩
theorem dir370_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 .east p = true := by
  change ((!walkGuard soko1_2.board support p 370 371 .east || decide (bonus 370 p ≤ bonus 371 p)) && ((PreciseRolling.stayTargets soko1_2.board 371 .east).all (fun landing => !pushGuard support p 370 371 372 landing || decide (bonus 370 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some landing)))) && (pushTargets soko1_2.board 371 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 370 371 372 landing || decide (bonus 370 p ≤ 1 - Generated.soko1_2Potential.boulder 371 - Generated.soko1_2Potential.hole landing + bonus 371 (change p 371 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1043 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1044 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir370_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 .west p = true := by
  rfl
theorem dir370_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 370 345 .northEast || decide (bonus 370 p ≤ bonus 345 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1045 p, rfl⟩
theorem dir370_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 .northWest p = true := by
  rfl
theorem dir370_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 370 397 .southEast || decide (bonus 370 p ≤ bonus 397 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1046 p, rfl⟩
theorem dir370_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 370 .southWest p = true := by
  rfl
theorem dir371_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 .north p = true := by
  change ((!walkGuard soko1_2.board support p 371 345 .north || decide (bonus 371 p ≤ bonus 345 p)) && ((PreciseRolling.stayTargets soko1_2.board 345 .north).all (fun landing => !pushGuard support p 371 345 319 landing || decide (bonus 371 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 345 + bonus 345 (change p 345 (some landing)))) && (pushTargets soko1_2.board 345 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 371 345 319 landing || decide (bonus 371 p ≤ 1 - Generated.soko1_2Potential.boulder 345 - Generated.soko1_2Potential.hole landing + bonus 345 (change p 345 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1047 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1048 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir371_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 .south p = true := by
  change ((!walkGuard soko1_2.board support p 371 397 .south || decide (bonus 371 p ≤ bonus 397 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1049 p, rfl⟩
theorem dir371_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 .east p = true := by
  change ((!walkGuard soko1_2.board support p 371 372 .east || decide (bonus 371 p ≤ bonus 372 p)) && ((PreciseRolling.stayTargets soko1_2.board 372 .east).all (fun landing => !pushGuard support p 371 372 373 landing || decide (bonus 371 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 372 + bonus 372 (change p 372 (some landing)))) && (pushTargets soko1_2.board 372 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 371 372 373 landing || decide (bonus 371 p ≤ 1 - Generated.soko1_2Potential.boulder 372 - Generated.soko1_2Potential.hole landing + bonus 372 (change p 372 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1050 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1051 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir371_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 .west p = true := by
  change ((!walkGuard soko1_2.board support p 371 370 .west || decide (bonus 371 p ≤ bonus 370 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1052 p, rfl⟩
theorem dir371_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 .northEast p = true := by
  rfl
theorem dir371_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 .northWest p = true := by
  rfl
theorem dir371_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 .southEast p = true := by
  rfl
theorem dir371_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 371 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 371 396 .southWest || decide (bonus 371 p ≤ bonus 396 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1053 p, rfl⟩
theorem dir372_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 .north p = true := by
  rfl
theorem dir372_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 .south p = true := by
  rfl
theorem dir372_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 .east p = true := by
  change ((!walkGuard soko1_2.board support p 372 373 .east || decide (bonus 372 p ≤ bonus 373 p)) && ((PreciseRolling.stayTargets soko1_2.board 373 .east).all (fun landing => !pushGuard support p 372 373 374 landing || decide (bonus 372 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 373 + bonus 373 (change p 373 (some landing)))) && (pushTargets soko1_2.board 373 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 372 373 374 landing || decide (bonus 372 p ≤ 1 - Generated.soko1_2Potential.boulder 373 - Generated.soko1_2Potential.hole landing + bonus 373 (change p 373 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1054 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1055 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir372_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 .west p = true := by
  change ((!walkGuard soko1_2.board support p 372 371 .west || decide (bonus 372 p ≤ bonus 371 p)) && ((PreciseRolling.stayTargets soko1_2.board 371 .west).all (fun landing => !pushGuard support p 372 371 370 landing || decide (bonus 372 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some landing)))) && (pushTargets soko1_2.board 371 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 372 371 370 landing || decide (bonus 372 p ≤ 1 - Generated.soko1_2Potential.boulder 371 - Generated.soko1_2Potential.hole landing + bonus 371 (change p 371 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1056 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1057 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir372_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 .northEast p = true := by
  rfl
theorem dir372_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 372 345 .northWest || decide (bonus 372 p ≤ bonus 345 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1058 p, rfl⟩
theorem dir372_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 372 399 .southEast || decide (bonus 372 p ≤ bonus 399 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1059 p, rfl⟩
theorem dir372_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 372 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 372 397 .southWest || decide (bonus 372 p ≤ bonus 397 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1060 p, rfl⟩
end NetHack.Sokoban12CostPartition
