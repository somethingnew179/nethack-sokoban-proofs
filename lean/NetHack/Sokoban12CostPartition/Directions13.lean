import NetHack.Sokoban12CostPartition.Directions12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir236_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 .north p = true := by
  change ((!walkGuard soko1_2.board support p 236 210 .north || decide (bonus 236 p ≤ bonus 210 p)) && ((PreciseRolling.stayTargets soko1_2.board 210 .north).all (fun landing => !pushGuard support p 236 210 184 landing || decide (bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 210 + bonus 210 (change p 210 (some landing)))) && (pushTargets soko1_2.board 210 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 236 210 184 landing || decide (bonus 236 p ≤ 1 - Generated.soko1_2Potential.boulder 210 - Generated.soko1_2Potential.hole landing + bonus 210 (change p 210 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check566 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check567 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir236_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 .south p = true := by
  change ((!walkGuard soko1_2.board support p 236 262 .south || decide (bonus 236 p ≤ bonus 262 p)) && ((PreciseRolling.stayTargets soko1_2.board 262 .south).all (fun landing => !pushGuard support p 236 262 288 landing || decide (bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 262 + bonus 262 (change p 262 (some landing)))) && (pushTargets soko1_2.board 262 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 236 262 288 landing || decide (bonus 236 p ≤ 1 - Generated.soko1_2Potential.boulder 262 - Generated.soko1_2Potential.hole landing + bonus 262 (change p 262 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check568 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check569 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir236_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 .east p = true := by
  change ((!walkGuard soko1_2.board support p 236 237 .east || decide (bonus 236 p ≤ bonus 237 p)) && ((PreciseRolling.stayTargets soko1_2.board 237 .east).all (fun landing => !pushGuard support p 236 237 238 landing || decide (bonus 236 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some landing)))) && (pushTargets soko1_2.board 237 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 236 237 238 landing || decide (bonus 236 p ≤ 1 - Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.hole landing + bonus 237 (change p 237 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check570 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check571 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir236_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 .west p = true := by
  rfl
theorem dir236_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 236 211 .northEast || decide (bonus 236 p ≤ bonus 211 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check572 p, rfl⟩
theorem dir236_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 .northWest p = true := by
  rfl
theorem dir236_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 236 263 .southEast || decide (bonus 236 p ≤ bonus 263 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check573 p, rfl⟩
theorem dir236_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 236 .southWest p = true := by
  rfl
theorem dir237_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 .north p = true := by
  change ((!walkGuard soko1_2.board support p 237 211 .north || decide (bonus 237 p ≤ bonus 211 p)) && ((PreciseRolling.stayTargets soko1_2.board 211 .north).all (fun landing => !pushGuard support p 237 211 185 landing || decide (bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some landing)))) && (pushTargets soko1_2.board 211 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 237 211 185 landing || decide (bonus 237 p ≤ 1 - Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.hole landing + bonus 211 (change p 211 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check574 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check575 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir237_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 .south p = true := by
  change ((!walkGuard soko1_2.board support p 237 263 .south || decide (bonus 237 p ≤ bonus 263 p)) && ((PreciseRolling.stayTargets soko1_2.board 263 .south).all (fun landing => !pushGuard support p 237 263 289 landing || decide (bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some landing)))) && (pushTargets soko1_2.board 263 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 237 263 289 landing || decide (bonus 237 p ≤ 1 - Generated.soko1_2Potential.boulder 263 - Generated.soko1_2Potential.hole landing + bonus 263 (change p 263 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check576 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check577 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir237_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 .east p = true := by
  change ((!walkGuard soko1_2.board support p 237 238 .east || decide (bonus 237 p ≤ bonus 238 p)) && ((PreciseRolling.stayTargets soko1_2.board 238 .east).all (fun landing => !pushGuard support p 237 238 239 landing || decide (bonus 237 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some landing)))) && (pushTargets soko1_2.board 238 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 237 238 239 landing || decide (bonus 237 p ≤ 1 - Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.hole landing + bonus 238 (change p 238 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check578 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check579 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir237_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 .west p = true := by
  change ((!walkGuard soko1_2.board support p 237 236 .west || decide (bonus 237 p ≤ bonus 236 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check580 p, rfl⟩
theorem dir237_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 237 212 .northEast || decide (bonus 237 p ≤ bonus 212 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check581 p, rfl⟩
theorem dir237_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 237 210 .northWest || decide (bonus 237 p ≤ bonus 210 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check582 p, rfl⟩
theorem dir237_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 237 264 .southEast || decide (bonus 237 p ≤ bonus 264 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check583 p, rfl⟩
theorem dir237_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 237 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 237 262 .southWest || decide (bonus 237 p ≤ bonus 262 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check584 p, rfl⟩
theorem dir238_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 .north p = true := by
  change ((!walkGuard soko1_2.board support p 238 212 .north || decide (bonus 238 p ≤ bonus 212 p)) && ((PreciseRolling.stayTargets soko1_2.board 212 .north).all (fun landing => !pushGuard support p 238 212 186 landing || decide (bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some landing)))) && (pushTargets soko1_2.board 212 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 238 212 186 landing || decide (bonus 238 p ≤ 1 - Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.hole landing + bonus 212 (change p 212 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check585 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check586 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir238_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 .south p = true := by
  change ((!walkGuard soko1_2.board support p 238 264 .south || decide (bonus 238 p ≤ bonus 264 p)) && ((PreciseRolling.stayTargets soko1_2.board 264 .south).all (fun landing => !pushGuard support p 238 264 290 landing || decide (bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some landing)))) && (pushTargets soko1_2.board 264 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 238 264 290 landing || decide (bonus 238 p ≤ 1 - Generated.soko1_2Potential.boulder 264 - Generated.soko1_2Potential.hole landing + bonus 264 (change p 264 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check587 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check588 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir238_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 .east p = true := by
  change ((!walkGuard soko1_2.board support p 238 239 .east || decide (bonus 238 p ≤ bonus 239 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check589 p, rfl⟩
theorem dir238_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 .west p = true := by
  change ((!walkGuard soko1_2.board support p 238 237 .west || decide (bonus 238 p ≤ bonus 237 p)) && ((PreciseRolling.stayTargets soko1_2.board 237 .west).all (fun landing => !pushGuard support p 238 237 236 landing || decide (bonus 238 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some landing)))) && (pushTargets soko1_2.board 237 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 238 237 236 landing || decide (bonus 238 p ≤ 1 - Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.hole landing + bonus 237 (change p 237 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check590 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check591 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir238_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 238 213 .northEast || decide (bonus 238 p ≤ bonus 213 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check592 p, rfl⟩
theorem dir238_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 238 211 .northWest || decide (bonus 238 p ≤ bonus 211 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check593 p, rfl⟩
theorem dir238_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 238 265 .southEast || decide (bonus 238 p ≤ bonus 265 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check594 p, rfl⟩
theorem dir238_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 238 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 238 263 .southWest || decide (bonus 238 p ≤ bonus 263 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check595 p, rfl⟩
theorem dir239_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 .north p = true := by
  change ((!walkGuard soko1_2.board support p 239 213 .north || decide (bonus 239 p ≤ bonus 213 p)) && ((PreciseRolling.stayTargets soko1_2.board 213 .north).all (fun landing => !pushGuard support p 239 213 187 landing || decide (bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some landing)))) && (pushTargets soko1_2.board 213 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 239 213 187 landing || decide (bonus 239 p ≤ 1 - Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.hole landing + bonus 213 (change p 213 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check596 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check597 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir239_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 .south p = true := by
  change ((!walkGuard soko1_2.board support p 239 265 .south || decide (bonus 239 p ≤ bonus 265 p)) && ((PreciseRolling.stayTargets soko1_2.board 265 .south).all (fun landing => !pushGuard support p 239 265 291 landing || decide (bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 265 + bonus 265 (change p 265 (some landing)))) && (pushTargets soko1_2.board 265 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 239 265 291 landing || decide (bonus 239 p ≤ 1 - Generated.soko1_2Potential.boulder 265 - Generated.soko1_2Potential.hole landing + bonus 265 (change p 265 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check598 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check599 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir239_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 .east p = true := by
  rfl
theorem dir239_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 .west p = true := by
  change ((!walkGuard soko1_2.board support p 239 238 .west || decide (bonus 239 p ≤ bonus 238 p)) && ((PreciseRolling.stayTargets soko1_2.board 238 .west).all (fun landing => !pushGuard support p 239 238 237 landing || decide (bonus 239 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some landing)))) && (pushTargets soko1_2.board 238 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 239 238 237 landing || decide (bonus 239 p ≤ 1 - Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.hole landing + bonus 238 (change p 238 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check600 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check601 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir239_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 239 214 .northEast || decide (bonus 239 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check602 p, rfl⟩
theorem dir239_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 239 212 .northWest || decide (bonus 239 p ≤ bonus 212 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check603 p, rfl⟩
theorem dir239_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 .southEast p = true := by
  rfl
theorem dir239_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 239 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 239 264 .southWest || decide (bonus 239 p ≤ bonus 264 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check604 p, rfl⟩
theorem dir241_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 .north p = true := by
  change ((!walkGuard soko1_2.board support p 241 215 .north || decide (bonus 241 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko1_2.board 215 .north).all (fun landing => !pushGuard support p 241 215 189 landing || decide (bonus 241 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko1_2.board 215 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 241 215 189 landing || decide (bonus 241 p ≤ 1 - Generated.soko1_2Potential.boulder 215 - Generated.soko1_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check605 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check606 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir241_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 .south p = true := by
  rfl
theorem dir241_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 .east p = true := by
  change ((!walkGuard soko1_2.board support p 241 242 .east || decide (bonus 241 p ≤ bonus 242 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check607 p, rfl⟩
theorem dir241_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 .west p = true := by
  rfl
theorem dir241_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 241 216 .northEast || decide (bonus 241 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check608 p, rfl⟩
theorem dir241_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 241 214 .northWest || decide (bonus 241 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check609 p, rfl⟩
theorem dir241_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 .southEast p = true := by
  rfl
theorem dir241_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 241 .southWest p = true := by
  rfl
theorem dir242_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 .north p = true := by
  change ((!walkGuard soko1_2.board support p 242 216 .north || decide (bonus 242 p ≤ bonus 216 p)) && ((PreciseRolling.stayTargets soko1_2.board 216 .north).all (fun landing => !pushGuard support p 242 216 190 landing || decide (bonus 242 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 216 + bonus 216 (change p 216 (some landing)))) && (pushTargets soko1_2.board 216 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 242 216 190 landing || decide (bonus 242 p ≤ 1 - Generated.soko1_2Potential.boulder 216 - Generated.soko1_2Potential.hole landing + bonus 216 (change p 216 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check610 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check611 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir242_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 .south p = true := by
  rfl
theorem dir242_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 .east p = true := by
  rfl
theorem dir242_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 .west p = true := by
  change ((!walkGuard soko1_2.board support p 242 241 .west || decide (bonus 242 p ≤ bonus 241 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check612 p, rfl⟩
theorem dir242_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 .northEast p = true := by
  rfl
theorem dir242_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 242 215 .northWest || decide (bonus 242 p ≤ bonus 215 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check613 p, rfl⟩
theorem dir242_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 .southEast p = true := by
  rfl
theorem dir242_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 242 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
