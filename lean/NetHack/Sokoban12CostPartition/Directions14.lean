import NetHack.Sokoban12CostPartition.Directions13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir244_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 .north p = true := by
  change ((!walkGuard soko1_2.board support p 244 218 .north || decide (bonus 244 p ≤ bonus 218 p)) && ((PreciseRolling.stayTargets soko1_2.board 218 .north).all (fun landing => !pushGuard support p 244 218 192 landing || decide (bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 218 + bonus 218 (change p 218 (some landing)))) && (pushTargets soko1_2.board 218 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 244 218 192 landing || decide (bonus 244 p ≤ 1 - Generated.soko1_2Potential.boulder 218 - Generated.soko1_2Potential.hole landing + bonus 218 (change p 218 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check614 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check615 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir244_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 .south p = true := by
  change ((!walkGuard soko1_2.board support p 244 270 .south || decide (bonus 244 p ≤ bonus 270 p)) && ((PreciseRolling.stayTargets soko1_2.board 270 .south).all (fun landing => !pushGuard support p 244 270 296 landing || decide (bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 270 + bonus 270 (change p 270 (some landing)))) && (pushTargets soko1_2.board 270 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 244 270 296 landing || decide (bonus 244 p ≤ 1 - Generated.soko1_2Potential.boulder 270 - Generated.soko1_2Potential.hole landing + bonus 270 (change p 270 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check616 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check617 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir244_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 .east p = true := by
  change ((!walkGuard soko1_2.board support p 244 245 .east || decide (bonus 244 p ≤ bonus 245 p)) && ((PreciseRolling.stayTargets soko1_2.board 245 .east).all (fun landing => !pushGuard support p 244 245 246 landing || decide (bonus 244 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some landing)))) && (pushTargets soko1_2.board 245 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 244 245 246 landing || decide (bonus 244 p ≤ 1 - Generated.soko1_2Potential.boulder 245 - Generated.soko1_2Potential.hole landing + bonus 245 (change p 245 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check618 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check619 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir244_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 .west p = true := by
  rfl
theorem dir244_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 244 219 .northEast || decide (bonus 244 p ≤ bonus 219 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check620 p, rfl⟩
theorem dir244_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 .northWest p = true := by
  rfl
theorem dir244_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 244 271 .southEast || decide (bonus 244 p ≤ bonus 271 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check621 p, rfl⟩
theorem dir244_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 244 .southWest p = true := by
  rfl
theorem dir245_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 .north p = true := by
  change ((!walkGuard soko1_2.board support p 245 219 .north || decide (bonus 245 p ≤ bonus 219 p)) && ((PreciseRolling.stayTargets soko1_2.board 219 .north).all (fun landing => !pushGuard support p 245 219 193 landing || decide (bonus 245 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some landing)))) && (pushTargets soko1_2.board 219 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 245 219 193 landing || decide (bonus 245 p ≤ 1 - Generated.soko1_2Potential.boulder 219 - Generated.soko1_2Potential.hole landing + bonus 219 (change p 219 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check622 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check623 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir245_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 .south p = true := by
  change ((!walkGuard soko1_2.board support p 245 271 .south || decide (bonus 245 p ≤ bonus 271 p)) && ((PreciseRolling.stayTargets soko1_2.board 271 .south).all (fun landing => !pushGuard support p 245 271 297 landing || decide (bonus 245 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 271 + bonus 271 (change p 271 (some landing)))) && (pushTargets soko1_2.board 271 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 245 271 297 landing || decide (bonus 245 p ≤ 1 - Generated.soko1_2Potential.boulder 271 - Generated.soko1_2Potential.hole landing + bonus 271 (change p 271 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check624 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check625 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir245_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 .east p = true := by
  change ((!walkGuard soko1_2.board support p 245 246 .east || decide (bonus 245 p ≤ bonus 246 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check626 p, rfl⟩
theorem dir245_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 .west p = true := by
  change ((!walkGuard soko1_2.board support p 245 244 .west || decide (bonus 245 p ≤ bonus 244 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check627 p, rfl⟩
theorem dir245_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 245 220 .northEast || decide (bonus 245 p ≤ bonus 220 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check628 p, rfl⟩
theorem dir245_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 245 218 .northWest || decide (bonus 245 p ≤ bonus 218 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check629 p, rfl⟩
theorem dir245_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 245 272 .southEast || decide (bonus 245 p ≤ bonus 272 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check630 p, rfl⟩
theorem dir245_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 245 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 245 270 .southWest || decide (bonus 245 p ≤ bonus 270 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check631 p, rfl⟩
theorem dir246_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 .north p = true := by
  change ((!walkGuard soko1_2.board support p 246 220 .north || decide (bonus 246 p ≤ bonus 220 p)) && ((PreciseRolling.stayTargets soko1_2.board 220 .north).all (fun landing => !pushGuard support p 246 220 194 landing || decide (bonus 246 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 220 + bonus 220 (change p 220 (some landing)))) && (pushTargets soko1_2.board 220 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 246 220 194 landing || decide (bonus 246 p ≤ 1 - Generated.soko1_2Potential.boulder 220 - Generated.soko1_2Potential.hole landing + bonus 220 (change p 220 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check632 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check633 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir246_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 .south p = true := by
  change ((!walkGuard soko1_2.board support p 246 272 .south || decide (bonus 246 p ≤ bonus 272 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check634 p, rfl⟩
theorem dir246_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 .east p = true := by
  rfl
theorem dir246_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 .west p = true := by
  change ((!walkGuard soko1_2.board support p 246 245 .west || decide (bonus 246 p ≤ bonus 245 p)) && ((PreciseRolling.stayTargets soko1_2.board 245 .west).all (fun landing => !pushGuard support p 246 245 244 landing || decide (bonus 246 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some landing)))) && (pushTargets soko1_2.board 245 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 246 245 244 landing || decide (bonus 246 p ≤ 1 - Generated.soko1_2Potential.boulder 245 - Generated.soko1_2Potential.hole landing + bonus 245 (change p 245 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check635 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check636 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir246_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 .northEast p = true := by
  rfl
theorem dir246_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 246 219 .northWest || decide (bonus 246 p ≤ bonus 219 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check637 p, rfl⟩
theorem dir246_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 .southEast p = true := by
  rfl
theorem dir246_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 246 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 246 271 .southWest || decide (bonus 246 p ≤ bonus 271 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check638 p, rfl⟩
theorem dir252_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 .north p = true := by
  rfl
theorem dir252_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 .south p = true := by
  change ((!walkGuard soko1_2.board support p 252 278 .south || decide (bonus 252 p ≤ bonus 278 p)) && ((PreciseRolling.stayTargets soko1_2.board 278 .south).all (fun landing => !pushGuard support p 252 278 304 landing || decide (bonus 252 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 278 + bonus 278 (change p 278 (some landing)))) && (pushTargets soko1_2.board 278 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 252 278 304 landing || decide (bonus 252 p ≤ 1 - Generated.soko1_2Potential.boulder 278 - Generated.soko1_2Potential.hole landing + bonus 278 (change p 278 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check639 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check640 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir252_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 .east p = true := by
  change ((!walkGuard soko1_2.board support p 252 253 .east || decide (bonus 252 p ≤ bonus 253 p)) && ((PreciseRolling.stayTargets soko1_2.board 253 .east).all (fun landing => !pushGuard support p 252 253 254 landing || decide (bonus 252 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 253 + bonus 253 (change p 253 (some landing)))) && (pushTargets soko1_2.board 253 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 252 253 254 landing || decide (bonus 252 p ≤ 1 - Generated.soko1_2Potential.boulder 253 - Generated.soko1_2Potential.hole landing + bonus 253 (change p 253 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check641 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check642 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir252_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 .west p = true := by
  rfl
theorem dir252_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 .northEast p = true := by
  rfl
theorem dir252_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 .northWest p = true := by
  rfl
theorem dir252_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 252 279 .southEast || decide (bonus 252 p ≤ bonus 279 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check643 p, rfl⟩
theorem dir252_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 252 .southWest p = true := by
  rfl
theorem dir253_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 .north p = true := by
  rfl
theorem dir253_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 .south p = true := by
  change ((!walkGuard soko1_2.board support p 253 279 .south || decide (bonus 253 p ≤ bonus 279 p)) && ((PreciseRolling.stayTargets soko1_2.board 279 .south).all (fun landing => !pushGuard support p 253 279 305 landing || decide (bonus 253 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some landing)))) && (pushTargets soko1_2.board 279 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 253 279 305 landing || decide (bonus 253 p ≤ 1 - Generated.soko1_2Potential.boulder 279 - Generated.soko1_2Potential.hole landing + bonus 279 (change p 279 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check644 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check645 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir253_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 .east p = true := by
  change ((!walkGuard soko1_2.board support p 253 254 .east || decide (bonus 253 p ≤ bonus 254 p)) && ((PreciseRolling.stayTargets soko1_2.board 254 .east).all (fun landing => !pushGuard support p 253 254 255 landing || decide (bonus 253 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 254 + bonus 254 (change p 254 (some landing)))) && (pushTargets soko1_2.board 254 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 253 254 255 landing || decide (bonus 253 p ≤ 1 - Generated.soko1_2Potential.boulder 254 - Generated.soko1_2Potential.hole landing + bonus 254 (change p 254 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check646 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check647 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir253_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 .west p = true := by
  change ((!walkGuard soko1_2.board support p 253 252 .west || decide (bonus 253 p ≤ bonus 252 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check648 p, rfl⟩
theorem dir253_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 .northEast p = true := by
  rfl
theorem dir253_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 .northWest p = true := by
  rfl
theorem dir253_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 253 280 .southEast || decide (bonus 253 p ≤ bonus 280 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check649 p, rfl⟩
theorem dir253_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 253 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 253 278 .southWest || decide (bonus 253 p ≤ bonus 278 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check650 p, rfl⟩
theorem dir254_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 .north p = true := by
  rfl
theorem dir254_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 .south p = true := by
  change ((!walkGuard soko1_2.board support p 254 280 .south || decide (bonus 254 p ≤ bonus 280 p)) && ((PreciseRolling.stayTargets soko1_2.board 280 .south).all (fun landing => !pushGuard support p 254 280 306 landing || decide (bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some landing)))) && (pushTargets soko1_2.board 280 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 254 280 306 landing || decide (bonus 254 p ≤ 1 - Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.hole landing + bonus 280 (change p 280 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check651 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check652 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir254_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 .east p = true := by
  change ((!walkGuard soko1_2.board support p 254 255 .east || decide (bonus 254 p ≤ bonus 255 p)) && ((PreciseRolling.stayTargets soko1_2.board 255 .east).all (fun landing => !pushGuard support p 254 255 256 landing || decide (bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 255 + bonus 255 (change p 255 (some landing)))) && (pushTargets soko1_2.board 255 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 254 255 256 landing || decide (bonus 254 p ≤ 1 - Generated.soko1_2Potential.boulder 255 - Generated.soko1_2Potential.hole landing + bonus 255 (change p 255 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check653 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check654 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir254_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 .west p = true := by
  change ((!walkGuard soko1_2.board support p 254 253 .west || decide (bonus 254 p ≤ bonus 253 p)) && ((PreciseRolling.stayTargets soko1_2.board 253 .west).all (fun landing => !pushGuard support p 254 253 252 landing || decide (bonus 254 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 253 + bonus 253 (change p 253 (some landing)))) && (pushTargets soko1_2.board 253 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 254 253 252 landing || decide (bonus 254 p ≤ 1 - Generated.soko1_2Potential.boulder 253 - Generated.soko1_2Potential.hole landing + bonus 253 (change p 253 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check655 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check656 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir254_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 .northEast p = true := by
  rfl
theorem dir254_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 .northWest p = true := by
  rfl
theorem dir254_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 254 281 .southEast || decide (bonus 254 p ≤ bonus 281 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check657 p, rfl⟩
theorem dir254_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 254 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 254 279 .southWest || decide (bonus 254 p ≤ bonus 279 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check658 p, rfl⟩
end NetHack.Sokoban12CostPartition
