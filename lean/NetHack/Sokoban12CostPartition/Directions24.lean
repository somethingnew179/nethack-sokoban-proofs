import NetHack.Sokoban12CostPartition.Directions23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir373_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 .north p = true := by
  rfl
theorem dir373_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 .south p = true := by
  change ((!walkGuard soko1_2.board support p 373 399 .south || decide (bonus 373 p ≤ bonus 399 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1061 p, rfl⟩
theorem dir373_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 .east p = true := by
  change ((!walkGuard soko1_2.board support p 373 374 .east || decide (bonus 373 p ≤ bonus 374 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1062 p, rfl⟩
theorem dir373_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 .west p = true := by
  change ((!walkGuard soko1_2.board support p 373 372 .west || decide (bonus 373 p ≤ bonus 372 p)) && ((PreciseRolling.stayTargets soko1_2.board 372 .west).all (fun landing => !pushGuard support p 373 372 371 landing || decide (bonus 373 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 372 + bonus 372 (change p 372 (some landing)))) && (pushTargets soko1_2.board 372 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 373 372 371 landing || decide (bonus 373 p ≤ 1 - Generated.soko1_2Potential.boulder 372 - Generated.soko1_2Potential.hole landing + bonus 372 (change p 372 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1063 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1064 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir373_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 373 348 .northEast || decide (bonus 373 p ≤ bonus 348 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1065 p, rfl⟩
theorem dir373_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 .northWest p = true := by
  rfl
theorem dir373_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 373 400 .southEast || decide (bonus 373 p ≤ bonus 400 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1066 p, rfl⟩
theorem dir373_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 373 .southWest p = true := by
  rfl
theorem dir374_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 .north p = true := by
  change ((!walkGuard soko1_2.board support p 374 348 .north || decide (bonus 374 p ≤ bonus 348 p)) && ((PreciseRolling.stayTargets soko1_2.board 348 .north).all (fun landing => !pushGuard support p 374 348 322 landing || decide (bonus 374 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 348 + bonus 348 (change p 348 (some landing)))) && (pushTargets soko1_2.board 348 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 374 348 322 landing || decide (bonus 374 p ≤ 1 - Generated.soko1_2Potential.boulder 348 - Generated.soko1_2Potential.hole landing + bonus 348 (change p 348 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1067 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1068 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir374_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 .south p = true := by
  change ((!walkGuard soko1_2.board support p 374 400 .south || decide (bonus 374 p ≤ bonus 400 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1069 p, rfl⟩
theorem dir374_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 .east p = true := by
  rfl
theorem dir374_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 .west p = true := by
  change ((!walkGuard soko1_2.board support p 374 373 .west || decide (bonus 374 p ≤ bonus 373 p)) && ((PreciseRolling.stayTargets soko1_2.board 373 .west).all (fun landing => !pushGuard support p 374 373 372 landing || decide (bonus 374 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 373 + bonus 373 (change p 373 (some landing)))) && (pushTargets soko1_2.board 373 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 374 373 372 landing || decide (bonus 374 p ≤ 1 - Generated.soko1_2Potential.boulder 373 - Generated.soko1_2Potential.hole landing + bonus 373 (change p 373 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1070 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1071 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir374_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 .northEast p = true := by
  rfl
theorem dir374_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 .northWest p = true := by
  rfl
theorem dir374_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 .southEast p = true := by
  rfl
theorem dir374_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 374 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 374 399 .southWest || decide (bonus 374 p ≤ bonus 399 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1072 p, rfl⟩
theorem dir380_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 .north p = true := by
  rfl
theorem dir380_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 .south p = true := by
  rfl
theorem dir380_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 .east p = true := by
  rfl
theorem dir380_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 .west p = true := by
  rfl
theorem dir380_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 .northEast p = true := by
  rfl
theorem dir380_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 .northWest p = true := by
  rfl
theorem dir380_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 .southEast p = true := by
  rfl
theorem dir380_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 380 .southWest p = true := by
  rfl
theorem dir382_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 .north p = true := by
  change ((!walkGuard soko1_2.board support p 382 356 .north || decide (bonus 382 p ≤ bonus 356 p)) && ((PreciseRolling.stayTargets soko1_2.board 356 .north).all (fun landing => !pushGuard support p 382 356 330 landing || decide (bonus 382 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 356 + bonus 356 (change p 356 (some landing)))) && (pushTargets soko1_2.board 356 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 382 356 330 landing || decide (bonus 382 p ≤ 1 - Generated.soko1_2Potential.boulder 356 - Generated.soko1_2Potential.hole landing + bonus 356 (change p 356 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1073 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1074 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir382_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 .south p = true := by
  change ((!walkGuard soko1_2.board support p 382 408 .south || decide (bonus 382 p ≤ bonus 408 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1075 p, rfl⟩
theorem dir382_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 .east p = true := by
  change ((!walkGuard soko1_2.board support p 382 383 .east || decide (bonus 382 p ≤ bonus 383 p)) && ((PreciseRolling.stayTargets soko1_2.board 383 .east).all (fun landing => !pushGuard support p 382 383 384 landing || decide (bonus 382 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some landing)))) && (pushTargets soko1_2.board 383 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 382 383 384 landing || decide (bonus 382 p ≤ 1 - Generated.soko1_2Potential.boulder 383 - Generated.soko1_2Potential.hole landing + bonus 383 (change p 383 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1076 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1077 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir382_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 .west p = true := by
  rfl
theorem dir382_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 382 357 .northEast || decide (bonus 382 p ≤ bonus 357 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1078 p, rfl⟩
theorem dir382_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 .northWest p = true := by
  rfl
theorem dir382_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 382 409 .southEast || decide (bonus 382 p ≤ bonus 409 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1079 p, rfl⟩
theorem dir382_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 382 .southWest p = true := by
  rfl
theorem dir383_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 .north p = true := by
  change ((!walkGuard soko1_2.board support p 383 357 .north || decide (bonus 383 p ≤ bonus 357 p)) && ((PreciseRolling.stayTargets soko1_2.board 357 .north).all (fun landing => !pushGuard support p 383 357 331 landing || decide (bonus 383 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 357 + bonus 357 (change p 357 (some landing)))) && (pushTargets soko1_2.board 357 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 383 357 331 landing || decide (bonus 383 p ≤ 1 - Generated.soko1_2Potential.boulder 357 - Generated.soko1_2Potential.hole landing + bonus 357 (change p 357 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1080 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1081 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir383_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 .south p = true := by
  change ((!walkGuard soko1_2.board support p 383 409 .south || decide (bonus 383 p ≤ bonus 409 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1082 p, rfl⟩
theorem dir383_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 .east p = true := by
  change ((!walkGuard soko1_2.board support p 383 384 .east || decide (bonus 383 p ≤ bonus 384 p)) && ((PreciseRolling.stayTargets soko1_2.board 384 .east).all (fun landing => !pushGuard support p 383 384 385 landing || decide (bonus 383 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some landing)))) && (pushTargets soko1_2.board 384 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 383 384 385 landing || decide (bonus 383 p ≤ 1 - Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.hole landing + bonus 384 (change p 384 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1083 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1084 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir383_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 .west p = true := by
  change ((!walkGuard soko1_2.board support p 383 382 .west || decide (bonus 383 p ≤ bonus 382 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1085 p, rfl⟩
theorem dir383_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 383 358 .northEast || decide (bonus 383 p ≤ bonus 358 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1086 p, rfl⟩
theorem dir383_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 383 356 .northWest || decide (bonus 383 p ≤ bonus 356 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1087 p, rfl⟩
theorem dir383_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 383 410 .southEast || decide (bonus 383 p ≤ bonus 410 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1088 p, rfl⟩
theorem dir383_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 383 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 383 408 .southWest || decide (bonus 383 p ≤ bonus 408 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1089 p, rfl⟩
theorem dir384_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 .north p = true := by
  change ((!walkGuard soko1_2.board support p 384 358 .north || decide (bonus 384 p ≤ bonus 358 p)) && ((PreciseRolling.stayTargets soko1_2.board 358 .north).all (fun landing => !pushGuard support p 384 358 332 landing || decide (bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 358 + bonus 358 (change p 358 (some landing)))) && (pushTargets soko1_2.board 358 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 384 358 332 landing || decide (bonus 384 p ≤ 1 - Generated.soko1_2Potential.boulder 358 - Generated.soko1_2Potential.hole landing + bonus 358 (change p 358 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1090 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1091 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir384_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 .south p = true := by
  change ((!walkGuard soko1_2.board support p 384 410 .south || decide (bonus 384 p ≤ bonus 410 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1092 p, rfl⟩
theorem dir384_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 .east p = true := by
  change ((!walkGuard soko1_2.board support p 384 385 .east || decide (bonus 384 p ≤ bonus 385 p)) && ((PreciseRolling.stayTargets soko1_2.board 385 .east).all (fun landing => !pushGuard support p 384 385 386 landing || decide (bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some landing)))) && (pushTargets soko1_2.board 385 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 384 385 386 landing || decide (bonus 384 p ≤ 1 - Generated.soko1_2Potential.boulder 385 - Generated.soko1_2Potential.hole landing + bonus 385 (change p 385 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1093 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1094 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir384_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 .west p = true := by
  change ((!walkGuard soko1_2.board support p 384 383 .west || decide (bonus 384 p ≤ bonus 383 p)) && ((PreciseRolling.stayTargets soko1_2.board 383 .west).all (fun landing => !pushGuard support p 384 383 382 landing || decide (bonus 384 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some landing)))) && (pushTargets soko1_2.board 383 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 384 383 382 landing || decide (bonus 384 p ≤ 1 - Generated.soko1_2Potential.boulder 383 - Generated.soko1_2Potential.hole landing + bonus 383 (change p 383 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1095 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1096 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir384_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 384 359 .northEast || decide (bonus 384 p ≤ bonus 359 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1097 p, rfl⟩
theorem dir384_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 384 357 .northWest || decide (bonus 384 p ≤ bonus 357 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1098 p, rfl⟩
theorem dir384_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 384 411 .southEast || decide (bonus 384 p ≤ bonus 411 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1099 p, rfl⟩
theorem dir384_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 384 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 384 409 .southWest || decide (bonus 384 p ≤ bonus 409 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1100 p, rfl⟩
end NetHack.Sokoban12CostPartition
