import NetHack.Sokoban12CostPartition.Directions18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir296_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 .north p = true := by
  change ((!walkGuard soko1_2.board support p 296 270 .north || decide (bonus 296 p ≤ bonus 270 p)) && ((PreciseRolling.stayTargets soko1_2.board 270 .north).all (fun landing => !pushGuard support p 296 270 244 landing || decide (bonus 296 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 270 + bonus 270 (change p 270 (some landing)))) && (pushTargets soko1_2.board 270 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 296 270 244 landing || decide (bonus 296 p ≤ 1 - Generated.soko1_2Potential.boulder 270 - Generated.soko1_2Potential.hole landing + bonus 270 (change p 270 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check831 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check832 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir296_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 .south p = true := by
  change ((!walkGuard soko1_2.board support p 296 322 .south || decide (bonus 296 p ≤ bonus 322 p)) && ((PreciseRolling.stayTargets soko1_2.board 322 .south).all (fun landing => !pushGuard support p 296 322 348 landing || decide (bonus 296 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 322 + bonus 322 (change p 322 (some landing)))) && (pushTargets soko1_2.board 322 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 296 322 348 landing || decide (bonus 296 p ≤ 1 - Generated.soko1_2Potential.boulder 322 - Generated.soko1_2Potential.hole landing + bonus 322 (change p 322 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check833 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check834 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir296_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 .east p = true := by
  change ((!walkGuard soko1_2.board support p 296 297 .east || decide (bonus 296 p ≤ bonus 297 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check835 p, rfl⟩
theorem dir296_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 .west p = true := by
  rfl
theorem dir296_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 296 271 .northEast || decide (bonus 296 p ≤ bonus 271 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check836 p, rfl⟩
theorem dir296_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 .northWest p = true := by
  rfl
theorem dir296_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 .southEast p = true := by
  rfl
theorem dir296_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 296 .southWest p = true := by
  rfl
theorem dir297_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 .north p = true := by
  change ((!walkGuard soko1_2.board support p 297 271 .north || decide (bonus 297 p ≤ bonus 271 p)) && ((PreciseRolling.stayTargets soko1_2.board 271 .north).all (fun landing => !pushGuard support p 297 271 245 landing || decide (bonus 297 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some landing)))) && (pushTargets soko1_2.board 271 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 297 271 245 landing || decide (bonus 297 p ≤ 1 - Generated.soko1_2Potential.boulder 271 - Generated.soko1_2Potential.hole landing + bonus 271 (change p 271 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check837 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check838 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir297_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 .south p = true := by
  rfl
theorem dir297_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 .east p = true := by
  rfl
theorem dir297_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 .west p = true := by
  change ((!walkGuard soko1_2.board support p 297 296 .west || decide (bonus 297 p ≤ bonus 296 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check839 p, rfl⟩
theorem dir297_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 297 272 .northEast || decide (bonus 297 p ≤ bonus 272 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check840 p, rfl⟩
theorem dir297_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 297 270 .northWest || decide (bonus 297 p ≤ bonus 270 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check841 p, rfl⟩
theorem dir297_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 .southEast p = true := by
  rfl
theorem dir297_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 297 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 297 322 .southWest || decide (bonus 297 p ≤ bonus 322 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check842 p, rfl⟩
theorem dir304_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 .north p = true := by
  change ((!walkGuard soko1_2.board support p 304 278 .north || decide (bonus 304 p ≤ bonus 278 p)) && ((PreciseRolling.stayTargets soko1_2.board 278 .north).all (fun landing => !pushGuard support p 304 278 252 landing || decide (bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 278 + bonus 278 (change p 278 (some landing)))) && (pushTargets soko1_2.board 278 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 304 278 252 landing || decide (bonus 304 p ≤ 1 - Generated.soko1_2Potential.boulder 278 - Generated.soko1_2Potential.hole landing + bonus 278 (change p 278 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check843 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check844 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir304_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 .south p = true := by
  change ((!walkGuard soko1_2.board support p 304 330 .south || decide (bonus 304 p ≤ bonus 330 p)) && ((PreciseRolling.stayTargets soko1_2.board 330 .south).all (fun landing => !pushGuard support p 304 330 356 landing || decide (bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 330 + bonus 330 (change p 330 (some landing)))) && (pushTargets soko1_2.board 330 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 304 330 356 landing || decide (bonus 304 p ≤ 1 - Generated.soko1_2Potential.boulder 330 - Generated.soko1_2Potential.hole landing + bonus 330 (change p 330 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check845 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check846 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir304_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 .east p = true := by
  change ((!walkGuard soko1_2.board support p 304 305 .east || decide (bonus 304 p ≤ bonus 305 p)) && ((PreciseRolling.stayTargets soko1_2.board 305 .east).all (fun landing => !pushGuard support p 304 305 306 landing || decide (bonus 304 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some landing)))) && (pushTargets soko1_2.board 305 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 304 305 306 landing || decide (bonus 304 p ≤ 1 - Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.hole landing + bonus 305 (change p 305 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check847 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check848 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir304_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 .west p = true := by
  rfl
theorem dir304_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 304 279 .northEast || decide (bonus 304 p ≤ bonus 279 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check849 p, rfl⟩
theorem dir304_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 .northWest p = true := by
  rfl
theorem dir304_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 304 331 .southEast || decide (bonus 304 p ≤ bonus 331 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check850 p, rfl⟩
theorem dir304_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 304 .southWest p = true := by
  rfl
theorem dir305_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 .north p = true := by
  change ((!walkGuard soko1_2.board support p 305 279 .north || decide (bonus 305 p ≤ bonus 279 p)) && ((PreciseRolling.stayTargets soko1_2.board 279 .north).all (fun landing => !pushGuard support p 305 279 253 landing || decide (bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some landing)))) && (pushTargets soko1_2.board 279 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 305 279 253 landing || decide (bonus 305 p ≤ 1 - Generated.soko1_2Potential.boulder 279 - Generated.soko1_2Potential.hole landing + bonus 279 (change p 279 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check851 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check852 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir305_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 .south p = true := by
  change ((!walkGuard soko1_2.board support p 305 331 .south || decide (bonus 305 p ≤ bonus 331 p)) && ((PreciseRolling.stayTargets soko1_2.board 331 .south).all (fun landing => !pushGuard support p 305 331 357 landing || decide (bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 331 + bonus 331 (change p 331 (some landing)))) && (pushTargets soko1_2.board 331 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 305 331 357 landing || decide (bonus 305 p ≤ 1 - Generated.soko1_2Potential.boulder 331 - Generated.soko1_2Potential.hole landing + bonus 331 (change p 331 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check853 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check854 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir305_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 .east p = true := by
  change ((!walkGuard soko1_2.board support p 305 306 .east || decide (bonus 305 p ≤ bonus 306 p)) && ((PreciseRolling.stayTargets soko1_2.board 306 .east).all (fun landing => !pushGuard support p 305 306 307 landing || decide (bonus 305 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some landing)))) && (pushTargets soko1_2.board 306 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 305 306 307 landing || decide (bonus 305 p ≤ 1 - Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.hole landing + bonus 306 (change p 306 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check855 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check856 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir305_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 .west p = true := by
  change ((!walkGuard soko1_2.board support p 305 304 .west || decide (bonus 305 p ≤ bonus 304 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check857 p, rfl⟩
theorem dir305_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 305 280 .northEast || decide (bonus 305 p ≤ bonus 280 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check858 p, rfl⟩
theorem dir305_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 305 278 .northWest || decide (bonus 305 p ≤ bonus 278 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check859 p, rfl⟩
theorem dir305_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 305 332 .southEast || decide (bonus 305 p ≤ bonus 332 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check860 p, rfl⟩
theorem dir305_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 305 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 305 330 .southWest || decide (bonus 305 p ≤ bonus 330 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check861 p, rfl⟩
theorem dir306_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 .north p = true := by
  change ((!walkGuard soko1_2.board support p 306 280 .north || decide (bonus 306 p ≤ bonus 280 p)) && ((PreciseRolling.stayTargets soko1_2.board 280 .north).all (fun landing => !pushGuard support p 306 280 254 landing || decide (bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some landing)))) && (pushTargets soko1_2.board 280 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 306 280 254 landing || decide (bonus 306 p ≤ 1 - Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.hole landing + bonus 280 (change p 280 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check862 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check863 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir306_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 .south p = true := by
  change ((!walkGuard soko1_2.board support p 306 332 .south || decide (bonus 306 p ≤ bonus 332 p)) && ((PreciseRolling.stayTargets soko1_2.board 332 .south).all (fun landing => !pushGuard support p 306 332 358 landing || decide (bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 332 + bonus 332 (change p 332 (some landing)))) && (pushTargets soko1_2.board 332 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 306 332 358 landing || decide (bonus 306 p ≤ 1 - Generated.soko1_2Potential.boulder 332 - Generated.soko1_2Potential.hole landing + bonus 332 (change p 332 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check864 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check865 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir306_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 .east p = true := by
  change ((!walkGuard soko1_2.board support p 306 307 .east || decide (bonus 306 p ≤ bonus 307 p)) && ((PreciseRolling.stayTargets soko1_2.board 307 .east).all (fun landing => !pushGuard support p 306 307 308 landing || decide (bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some landing)))) && (pushTargets soko1_2.board 307 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 306 307 308 landing || decide (bonus 306 p ≤ 1 - Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.hole landing + bonus 307 (change p 307 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check866 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check867 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir306_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 .west p = true := by
  change ((!walkGuard soko1_2.board support p 306 305 .west || decide (bonus 306 p ≤ bonus 305 p)) && ((PreciseRolling.stayTargets soko1_2.board 305 .west).all (fun landing => !pushGuard support p 306 305 304 landing || decide (bonus 306 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some landing)))) && (pushTargets soko1_2.board 305 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 306 305 304 landing || decide (bonus 306 p ≤ 1 - Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.hole landing + bonus 305 (change p 305 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check868 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check869 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir306_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 306 281 .northEast || decide (bonus 306 p ≤ bonus 281 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check870 p, rfl⟩
theorem dir306_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 306 279 .northWest || decide (bonus 306 p ≤ bonus 279 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check871 p, rfl⟩
theorem dir306_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 306 333 .southEast || decide (bonus 306 p ≤ bonus 333 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check872 p, rfl⟩
theorem dir306_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 306 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 306 331 .southWest || decide (bonus 306 p ≤ bonus 331 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check873 p, rfl⟩
theorem dir307_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 .north p = true := by
  change ((!walkGuard soko1_2.board support p 307 281 .north || decide (bonus 307 p ≤ bonus 281 p)) && ((PreciseRolling.stayTargets soko1_2.board 281 .north).all (fun landing => !pushGuard support p 307 281 255 landing || decide (bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some landing)))) && (pushTargets soko1_2.board 281 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 307 281 255 landing || decide (bonus 307 p ≤ 1 - Generated.soko1_2Potential.boulder 281 - Generated.soko1_2Potential.hole landing + bonus 281 (change p 281 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check874 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check875 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir307_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 .south p = true := by
  change ((!walkGuard soko1_2.board support p 307 333 .south || decide (bonus 307 p ≤ bonus 333 p)) && ((PreciseRolling.stayTargets soko1_2.board 333 .south).all (fun landing => !pushGuard support p 307 333 359 landing || decide (bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 333 + bonus 333 (change p 333 (some landing)))) && (pushTargets soko1_2.board 333 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 307 333 359 landing || decide (bonus 307 p ≤ 1 - Generated.soko1_2Potential.boulder 333 - Generated.soko1_2Potential.hole landing + bonus 333 (change p 333 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check876 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check877 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir307_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 .east p = true := by
  change ((!walkGuard soko1_2.board support p 307 308 .east || decide (bonus 307 p ≤ bonus 308 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check878 p, rfl⟩
theorem dir307_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 .west p = true := by
  change ((!walkGuard soko1_2.board support p 307 306 .west || decide (bonus 307 p ≤ bonus 306 p)) && ((PreciseRolling.stayTargets soko1_2.board 306 .west).all (fun landing => !pushGuard support p 307 306 305 landing || decide (bonus 307 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some landing)))) && (pushTargets soko1_2.board 306 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 307 306 305 landing || decide (bonus 307 p ≤ 1 - Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.hole landing + bonus 306 (change p 306 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check879 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check880 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir307_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 307 282 .northEast || decide (bonus 307 p ≤ bonus 282 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check881 p, rfl⟩
theorem dir307_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 307 280 .northWest || decide (bonus 307 p ≤ bonus 280 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check882 p, rfl⟩
theorem dir307_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 307 334 .southEast || decide (bonus 307 p ≤ bonus 334 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check883 p, rfl⟩
theorem dir307_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 307 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 307 332 .southWest || decide (bonus 307 p ≤ bonus 332 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check884 p, rfl⟩
end NetHack.Sokoban12CostPartition
