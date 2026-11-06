import NetHack.Sokoban12CostPartition.Directions24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir385_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 .north p = true := by
  change ((!walkGuard soko1_2.board support p 385 359 .north || decide (bonus 385 p ≤ bonus 359 p)) && ((PreciseRolling.stayTargets soko1_2.board 359 .north).all (fun landing => !pushGuard support p 385 359 333 landing || decide (bonus 385 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 359 + bonus 359 (change p 359 (some landing)))) && (pushTargets soko1_2.board 359 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 385 359 333 landing || decide (bonus 385 p ≤ 1 - Generated.soko1_2Potential.boulder 359 - Generated.soko1_2Potential.hole landing + bonus 359 (change p 359 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1101 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1102 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir385_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 .south p = true := by
  change ((!walkGuard soko1_2.board support p 385 411 .south || decide (bonus 385 p ≤ bonus 411 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1103 p, rfl⟩
theorem dir385_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 .east p = true := by
  change ((!walkGuard soko1_2.board support p 385 386 .east || decide (bonus 385 p ≤ bonus 386 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1104 p, rfl⟩
theorem dir385_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 .west p = true := by
  change ((!walkGuard soko1_2.board support p 385 384 .west || decide (bonus 385 p ≤ bonus 384 p)) && ((PreciseRolling.stayTargets soko1_2.board 384 .west).all (fun landing => !pushGuard support p 385 384 383 landing || decide (bonus 385 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some landing)))) && (pushTargets soko1_2.board 384 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 385 384 383 landing || decide (bonus 385 p ≤ 1 - Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.hole landing + bonus 384 (change p 384 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1105 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1106 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir385_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 385 360 .northEast || decide (bonus 385 p ≤ bonus 360 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1107 p, rfl⟩
theorem dir385_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 385 358 .northWest || decide (bonus 385 p ≤ bonus 358 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1108 p, rfl⟩
theorem dir385_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 385 412 .southEast || decide (bonus 385 p ≤ bonus 412 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1109 p, rfl⟩
theorem dir385_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 385 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 385 410 .southWest || decide (bonus 385 p ≤ bonus 410 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1110 p, rfl⟩
theorem dir386_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 .north p = true := by
  change ((!walkGuard soko1_2.board support p 386 360 .north || decide (bonus 386 p ≤ bonus 360 p)) && ((PreciseRolling.stayTargets soko1_2.board 360 .north).all (fun landing => !pushGuard support p 386 360 334 landing || decide (bonus 386 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 360 + bonus 360 (change p 360 (some landing)))) && (pushTargets soko1_2.board 360 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 386 360 334 landing || decide (bonus 386 p ≤ 1 - Generated.soko1_2Potential.boulder 360 - Generated.soko1_2Potential.hole landing + bonus 360 (change p 360 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1111 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1112 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir386_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 .south p = true := by
  change ((!walkGuard soko1_2.board support p 386 412 .south || decide (bonus 386 p ≤ bonus 412 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1113 p, rfl⟩
theorem dir386_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 .east p = true := by
  rfl
theorem dir386_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 .west p = true := by
  change ((!walkGuard soko1_2.board support p 386 385 .west || decide (bonus 386 p ≤ bonus 385 p)) && ((PreciseRolling.stayTargets soko1_2.board 385 .west).all (fun landing => !pushGuard support p 386 385 384 landing || decide (bonus 386 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some landing)))) && (pushTargets soko1_2.board 385 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 386 385 384 landing || decide (bonus 386 p ≤ 1 - Generated.soko1_2Potential.boulder 385 - Generated.soko1_2Potential.hole landing + bonus 385 (change p 385 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1114 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1115 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir386_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 .northEast p = true := by
  rfl
theorem dir386_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 386 359 .northWest || decide (bonus 386 p ≤ bonus 359 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1116 p, rfl⟩
theorem dir386_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 .southEast p = true := by
  rfl
theorem dir386_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 386 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 386 411 .southWest || decide (bonus 386 p ≤ bonus 411 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1117 p, rfl⟩
theorem dir396_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 .north p = true := by
  change ((!walkGuard soko1_2.board support p 396 370 .north || decide (bonus 396 p ≤ bonus 370 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1118 p, rfl⟩
theorem dir396_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 .south p = true := by
  rfl
theorem dir396_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 .east p = true := by
  change ((!walkGuard soko1_2.board support p 396 397 .east || decide (bonus 396 p ≤ bonus 397 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1119 p, rfl⟩
theorem dir396_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 .west p = true := by
  rfl
theorem dir396_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 396 371 .northEast || decide (bonus 396 p ≤ bonus 371 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1120 p, rfl⟩
theorem dir396_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 .northWest p = true := by
  rfl
theorem dir396_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 .southEast p = true := by
  rfl
theorem dir396_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 396 .southWest p = true := by
  rfl
theorem dir397_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 .north p = true := by
  change ((!walkGuard soko1_2.board support p 397 371 .north || decide (bonus 397 p ≤ bonus 371 p)) && ((PreciseRolling.stayTargets soko1_2.board 371 .north).all (fun landing => !pushGuard support p 397 371 345 landing || decide (bonus 397 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 371 + bonus 371 (change p 371 (some landing)))) && (pushTargets soko1_2.board 371 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 397 371 345 landing || decide (bonus 397 p ≤ 1 - Generated.soko1_2Potential.boulder 371 - Generated.soko1_2Potential.hole landing + bonus 371 (change p 371 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1121 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1122 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir397_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 .south p = true := by
  rfl
theorem dir397_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 .east p = true := by
  rfl
theorem dir397_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 .west p = true := by
  change ((!walkGuard soko1_2.board support p 397 396 .west || decide (bonus 397 p ≤ bonus 396 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1123 p, rfl⟩
theorem dir397_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 397 372 .northEast || decide (bonus 397 p ≤ bonus 372 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1124 p, rfl⟩
theorem dir397_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 397 370 .northWest || decide (bonus 397 p ≤ bonus 370 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1125 p, rfl⟩
theorem dir397_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 .southEast p = true := by
  rfl
theorem dir397_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 397 .southWest p = true := by
  rfl
theorem dir399_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 .north p = true := by
  change ((!walkGuard soko1_2.board support p 399 373 .north || decide (bonus 399 p ≤ bonus 373 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1126 p, rfl⟩
theorem dir399_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 .south p = true := by
  rfl
theorem dir399_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 .east p = true := by
  change ((!walkGuard soko1_2.board support p 399 400 .east || decide (bonus 399 p ≤ bonus 400 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1127 p, rfl⟩
theorem dir399_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 .west p = true := by
  rfl
theorem dir399_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 399 374 .northEast || decide (bonus 399 p ≤ bonus 374 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1128 p, rfl⟩
theorem dir399_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 399 372 .northWest || decide (bonus 399 p ≤ bonus 372 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1129 p, rfl⟩
theorem dir399_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 .southEast p = true := by
  rfl
theorem dir399_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 399 .southWest p = true := by
  rfl
theorem dir400_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 .north p = true := by
  change ((!walkGuard soko1_2.board support p 400 374 .north || decide (bonus 400 p ≤ bonus 374 p)) && ((PreciseRolling.stayTargets soko1_2.board 374 .north).all (fun landing => !pushGuard support p 400 374 348 landing || decide (bonus 400 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 374 + bonus 374 (change p 374 (some landing)))) && (pushTargets soko1_2.board 374 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 400 374 348 landing || decide (bonus 400 p ≤ 1 - Generated.soko1_2Potential.boulder 374 - Generated.soko1_2Potential.hole landing + bonus 374 (change p 374 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1130 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1131 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir400_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 .south p = true := by
  rfl
theorem dir400_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 .east p = true := by
  rfl
theorem dir400_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 .west p = true := by
  change ((!walkGuard soko1_2.board support p 400 399 .west || decide (bonus 400 p ≤ bonus 399 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1132 p, rfl⟩
theorem dir400_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 .northEast p = true := by
  rfl
theorem dir400_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 400 373 .northWest || decide (bonus 400 p ≤ bonus 373 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1133 p, rfl⟩
theorem dir400_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 .southEast p = true := by
  rfl
theorem dir400_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 400 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
