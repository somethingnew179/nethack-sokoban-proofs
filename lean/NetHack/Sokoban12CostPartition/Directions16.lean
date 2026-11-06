import NetHack.Sokoban12CostPartition.Directions15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir265_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 .north p = true := by
  change ((!walkGuard soko1_2.board support p 265 239 .north || decide (bonus 265 p ≤ bonus 239 p)) && ((PreciseRolling.stayTargets soko1_2.board 239 .north).all (fun landing => !pushGuard support p 265 239 213 landing || decide (bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 239 + bonus 239 (change p 239 (some landing)))) && (pushTargets soko1_2.board 239 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 265 239 213 landing || decide (bonus 265 p ≤ 1 - Generated.soko1_2Potential.boulder 239 - Generated.soko1_2Potential.hole landing + bonus 239 (change p 239 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check702 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check703 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir265_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 .south p = true := by
  change ((!walkGuard soko1_2.board support p 265 291 .south || decide (bonus 265 p ≤ bonus 291 p)) && ((PreciseRolling.stayTargets soko1_2.board 291 .south).all (fun landing => !pushGuard support p 265 291 317 landing || decide (bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some landing)))) && (pushTargets soko1_2.board 291 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 265 291 317 landing || decide (bonus 265 p ≤ 1 - Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.hole landing + bonus 291 (change p 291 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check704 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check705 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir265_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 .east p = true := by
  rfl
theorem dir265_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 .west p = true := by
  change ((!walkGuard soko1_2.board support p 265 264 .west || decide (bonus 265 p ≤ bonus 264 p)) && ((PreciseRolling.stayTargets soko1_2.board 264 .west).all (fun landing => !pushGuard support p 265 264 263 landing || decide (bonus 265 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some landing)))) && (pushTargets soko1_2.board 264 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 265 264 263 landing || decide (bonus 265 p ≤ 1 - Generated.soko1_2Potential.boulder 264 - Generated.soko1_2Potential.hole landing + bonus 264 (change p 264 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check706 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check707 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir265_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 .northEast p = true := by
  rfl
theorem dir265_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 265 238 .northWest || decide (bonus 265 p ≤ bonus 238 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check708 p, rfl⟩
theorem dir265_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 265 292 .southEast || decide (bonus 265 p ≤ bonus 292 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check709 p, rfl⟩
theorem dir265_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 265 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 265 290 .southWest || decide (bonus 265 p ≤ bonus 290 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check710 p, rfl⟩
theorem dir270_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 .north p = true := by
  change ((!walkGuard soko1_2.board support p 270 244 .north || decide (bonus 270 p ≤ bonus 244 p)) && ((PreciseRolling.stayTargets soko1_2.board 244 .north).all (fun landing => !pushGuard support p 270 244 218 landing || decide (bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 244 + bonus 244 (change p 244 (some landing)))) && (pushTargets soko1_2.board 244 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 270 244 218 landing || decide (bonus 270 p ≤ 1 - Generated.soko1_2Potential.boulder 244 - Generated.soko1_2Potential.hole landing + bonus 244 (change p 244 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check711 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check712 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir270_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 .south p = true := by
  change ((!walkGuard soko1_2.board support p 270 296 .south || decide (bonus 270 p ≤ bonus 296 p)) && ((PreciseRolling.stayTargets soko1_2.board 296 .south).all (fun landing => !pushGuard support p 270 296 322 landing || decide (bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 296 + bonus 296 (change p 296 (some landing)))) && (pushTargets soko1_2.board 296 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 270 296 322 landing || decide (bonus 270 p ≤ 1 - Generated.soko1_2Potential.boulder 296 - Generated.soko1_2Potential.hole landing + bonus 296 (change p 296 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check713 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check714 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir270_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 .east p = true := by
  change ((!walkGuard soko1_2.board support p 270 271 .east || decide (bonus 270 p ≤ bonus 271 p)) && ((PreciseRolling.stayTargets soko1_2.board 271 .east).all (fun landing => !pushGuard support p 270 271 272 landing || decide (bonus 270 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some landing)))) && (pushTargets soko1_2.board 271 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 270 271 272 landing || decide (bonus 270 p ≤ 1 - Generated.soko1_2Potential.boulder 271 - Generated.soko1_2Potential.hole landing + bonus 271 (change p 271 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check715 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check716 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir270_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 .west p = true := by
  rfl
theorem dir270_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 270 245 .northEast || decide (bonus 270 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check717 p, rfl⟩
theorem dir270_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 .northWest p = true := by
  rfl
theorem dir270_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 270 297 .southEast || decide (bonus 270 p ≤ bonus 297 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check718 p, rfl⟩
theorem dir270_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 270 .southWest p = true := by
  rfl
theorem dir271_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 .north p = true := by
  change ((!walkGuard soko1_2.board support p 271 245 .north || decide (bonus 271 p ≤ bonus 245 p)) && ((PreciseRolling.stayTargets soko1_2.board 245 .north).all (fun landing => !pushGuard support p 271 245 219 landing || decide (bonus 271 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some landing)))) && (pushTargets soko1_2.board 245 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 271 245 219 landing || decide (bonus 271 p ≤ 1 - Generated.soko1_2Potential.boulder 245 - Generated.soko1_2Potential.hole landing + bonus 245 (change p 245 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check719 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check720 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir271_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 .south p = true := by
  change ((!walkGuard soko1_2.board support p 271 297 .south || decide (bonus 271 p ≤ bonus 297 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check721 p, rfl⟩
theorem dir271_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 .east p = true := by
  change ((!walkGuard soko1_2.board support p 271 272 .east || decide (bonus 271 p ≤ bonus 272 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check722 p, rfl⟩
theorem dir271_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 .west p = true := by
  change ((!walkGuard soko1_2.board support p 271 270 .west || decide (bonus 271 p ≤ bonus 270 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check723 p, rfl⟩
theorem dir271_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 271 246 .northEast || decide (bonus 271 p ≤ bonus 246 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check724 p, rfl⟩
theorem dir271_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 271 244 .northWest || decide (bonus 271 p ≤ bonus 244 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check725 p, rfl⟩
theorem dir271_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 .southEast p = true := by
  rfl
theorem dir271_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 271 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 271 296 .southWest || decide (bonus 271 p ≤ bonus 296 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check726 p, rfl⟩
theorem dir272_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 .north p = true := by
  change ((!walkGuard soko1_2.board support p 272 246 .north || decide (bonus 272 p ≤ bonus 246 p)) && ((PreciseRolling.stayTargets soko1_2.board 246 .north).all (fun landing => !pushGuard support p 272 246 220 landing || decide (bonus 272 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 246 + bonus 246 (change p 246 (some landing)))) && (pushTargets soko1_2.board 246 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 272 246 220 landing || decide (bonus 272 p ≤ 1 - Generated.soko1_2Potential.boulder 246 - Generated.soko1_2Potential.hole landing + bonus 246 (change p 246 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check727 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check728 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir272_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 .south p = true := by
  rfl
theorem dir272_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 .east p = true := by
  rfl
theorem dir272_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 .west p = true := by
  change ((!walkGuard soko1_2.board support p 272 271 .west || decide (bonus 272 p ≤ bonus 271 p)) && ((PreciseRolling.stayTargets soko1_2.board 271 .west).all (fun landing => !pushGuard support p 272 271 270 landing || decide (bonus 272 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some landing)))) && (pushTargets soko1_2.board 271 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 272 271 270 landing || decide (bonus 272 p ≤ 1 - Generated.soko1_2Potential.boulder 271 - Generated.soko1_2Potential.hole landing + bonus 271 (change p 271 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check729 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check730 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir272_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 .northEast p = true := by
  rfl
theorem dir272_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 272 245 .northWest || decide (bonus 272 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check731 p, rfl⟩
theorem dir272_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 .southEast p = true := by
  rfl
theorem dir272_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 272 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 272 297 .southWest || decide (bonus 272 p ≤ bonus 297 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check732 p, rfl⟩
theorem dir276_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 .north p = true := by
  rfl
theorem dir276_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 .south p = true := by
  rfl
theorem dir276_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 .east p = true := by
  rfl
theorem dir276_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 .west p = true := by
  rfl
theorem dir276_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 .northEast p = true := by
  rfl
theorem dir276_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 .northWest p = true := by
  rfl
theorem dir276_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 .southEast p = true := by
  rfl
theorem dir276_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 276 .southWest p = true := by
  rfl
theorem dir278_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 .north p = true := by
  change ((!walkGuard soko1_2.board support p 278 252 .north || decide (bonus 278 p ≤ bonus 252 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check733 p, rfl⟩
theorem dir278_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 .south p = true := by
  change ((!walkGuard soko1_2.board support p 278 304 .south || decide (bonus 278 p ≤ bonus 304 p)) && ((PreciseRolling.stayTargets soko1_2.board 304 .south).all (fun landing => !pushGuard support p 278 304 330 landing || decide (bonus 278 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 304 + bonus 304 (change p 304 (some landing)))) && (pushTargets soko1_2.board 304 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 278 304 330 landing || decide (bonus 278 p ≤ 1 - Generated.soko1_2Potential.boulder 304 - Generated.soko1_2Potential.hole landing + bonus 304 (change p 304 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check734 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check735 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir278_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 .east p = true := by
  change ((!walkGuard soko1_2.board support p 278 279 .east || decide (bonus 278 p ≤ bonus 279 p)) && ((PreciseRolling.stayTargets soko1_2.board 279 .east).all (fun landing => !pushGuard support p 278 279 280 landing || decide (bonus 278 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some landing)))) && (pushTargets soko1_2.board 279 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 278 279 280 landing || decide (bonus 278 p ≤ 1 - Generated.soko1_2Potential.boulder 279 - Generated.soko1_2Potential.hole landing + bonus 279 (change p 279 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check736 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check737 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir278_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 .west p = true := by
  rfl
theorem dir278_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 278 253 .northEast || decide (bonus 278 p ≤ bonus 253 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check738 p, rfl⟩
theorem dir278_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 .northWest p = true := by
  rfl
theorem dir278_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 278 305 .southEast || decide (bonus 278 p ≤ bonus 305 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check739 p, rfl⟩
theorem dir278_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 278 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
