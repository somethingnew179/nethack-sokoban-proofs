import NetHack.Sokoban12CostPartition.Directions10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir206_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 .north p = true := by
  change ((!walkGuard soko1_2.board support p 206 180 .north || decide (bonus 206 p ≤ bonus 180 p)) && ((PreciseRolling.stayTargets soko1_2.board 180 .north).all (fun landing => !pushGuard support p 206 180 154 landing || decide (bonus 206 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 180 + bonus 180 (change p 180 (some landing)))) && (pushTargets soko1_2.board 180 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 206 180 154 landing || decide (bonus 206 p ≤ 1 - Generated.soko1_2Potential.boulder 180 - Generated.soko1_2Potential.hole landing + bonus 180 (change p 180 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check466 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check467 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir206_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 .south p = true := by
  change ((!walkGuard soko1_2.board support p 206 232 .south || decide (bonus 206 p ≤ bonus 232 p)) && ((PreciseRolling.stayTargets soko1_2.board 232 .south).all (fun landing => !pushGuard support p 206 232 258 landing || decide (bonus 206 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 232 + bonus 232 (change p 232 (some landing)))) && (pushTargets soko1_2.board 232 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 206 232 258 landing || decide (bonus 206 p ≤ 1 - Generated.soko1_2Potential.boulder 232 - Generated.soko1_2Potential.hole landing + bonus 232 (change p 232 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check468 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check469 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir206_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 .east p = true := by
  rfl
theorem dir206_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 .west p = true := by
  rfl
theorem dir206_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 .northEast p = true := by
  rfl
theorem dir206_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 .northWest p = true := by
  rfl
theorem dir206_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 .southEast p = true := by
  rfl
theorem dir206_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 206 .southWest p = true := by
  rfl
theorem dir210_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 .north p = true := by
  change ((!walkGuard soko1_2.board support p 210 184 .north || decide (bonus 210 p ≤ bonus 184 p)) && ((PreciseRolling.stayTargets soko1_2.board 184 .north).all (fun landing => !pushGuard support p 210 184 158 landing || decide (bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 184 + bonus 184 (change p 184 (some landing)))) && (pushTargets soko1_2.board 184 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 210 184 158 landing || decide (bonus 210 p ≤ 1 - Generated.soko1_2Potential.boulder 184 - Generated.soko1_2Potential.hole landing + bonus 184 (change p 184 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check470 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check471 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir210_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 .south p = true := by
  change ((!walkGuard soko1_2.board support p 210 236 .south || decide (bonus 210 p ≤ bonus 236 p)) && ((PreciseRolling.stayTargets soko1_2.board 236 .south).all (fun landing => !pushGuard support p 210 236 262 landing || decide (bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 236 + bonus 236 (change p 236 (some landing)))) && (pushTargets soko1_2.board 236 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 210 236 262 landing || decide (bonus 210 p ≤ 1 - Generated.soko1_2Potential.boulder 236 - Generated.soko1_2Potential.hole landing + bonus 236 (change p 236 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check472 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check473 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir210_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 .east p = true := by
  change ((!walkGuard soko1_2.board support p 210 211 .east || decide (bonus 210 p ≤ bonus 211 p)) && ((PreciseRolling.stayTargets soko1_2.board 211 .east).all (fun landing => !pushGuard support p 210 211 212 landing || decide (bonus 210 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some landing)))) && (pushTargets soko1_2.board 211 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 210 211 212 landing || decide (bonus 210 p ≤ 1 - Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.hole landing + bonus 211 (change p 211 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check474 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check475 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir210_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 .west p = true := by
  rfl
theorem dir210_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 210 185 .northEast || decide (bonus 210 p ≤ bonus 185 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check476 p, rfl⟩
theorem dir210_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 .northWest p = true := by
  rfl
theorem dir210_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 210 237 .southEast || decide (bonus 210 p ≤ bonus 237 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check477 p, rfl⟩
theorem dir210_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 210 .southWest p = true := by
  rfl
theorem dir211_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 .north p = true := by
  change ((!walkGuard soko1_2.board support p 211 185 .north || decide (bonus 211 p ≤ bonus 185 p)) && ((PreciseRolling.stayTargets soko1_2.board 185 .north).all (fun landing => !pushGuard support p 211 185 159 landing || decide (bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some landing)))) && (pushTargets soko1_2.board 185 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 211 185 159 landing || decide (bonus 211 p ≤ 1 - Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.hole landing + bonus 185 (change p 185 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check478 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check479 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir211_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 .south p = true := by
  change ((!walkGuard soko1_2.board support p 211 237 .south || decide (bonus 211 p ≤ bonus 237 p)) && ((PreciseRolling.stayTargets soko1_2.board 237 .south).all (fun landing => !pushGuard support p 211 237 263 landing || decide (bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some landing)))) && (pushTargets soko1_2.board 237 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 211 237 263 landing || decide (bonus 211 p ≤ 1 - Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.hole landing + bonus 237 (change p 237 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check480 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check481 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir211_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 .east p = true := by
  change ((!walkGuard soko1_2.board support p 211 212 .east || decide (bonus 211 p ≤ bonus 212 p)) && ((PreciseRolling.stayTargets soko1_2.board 212 .east).all (fun landing => !pushGuard support p 211 212 213 landing || decide (bonus 211 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some landing)))) && (pushTargets soko1_2.board 212 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 211 212 213 landing || decide (bonus 211 p ≤ 1 - Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.hole landing + bonus 212 (change p 212 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check482 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check483 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir211_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 .west p = true := by
  change ((!walkGuard soko1_2.board support p 211 210 .west || decide (bonus 211 p ≤ bonus 210 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check484 p, rfl⟩
theorem dir211_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 211 186 .northEast || decide (bonus 211 p ≤ bonus 186 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check485 p, rfl⟩
theorem dir211_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 211 184 .northWest || decide (bonus 211 p ≤ bonus 184 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check486 p, rfl⟩
theorem dir211_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 211 238 .southEast || decide (bonus 211 p ≤ bonus 238 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check487 p, rfl⟩
theorem dir211_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 211 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 211 236 .southWest || decide (bonus 211 p ≤ bonus 236 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check488 p, rfl⟩
theorem dir212_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 .north p = true := by
  change ((!walkGuard soko1_2.board support p 212 186 .north || decide (bonus 212 p ≤ bonus 186 p)) && ((PreciseRolling.stayTargets soko1_2.board 186 .north).all (fun landing => !pushGuard support p 212 186 160 landing || decide (bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some landing)))) && (pushTargets soko1_2.board 186 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 212 186 160 landing || decide (bonus 212 p ≤ 1 - Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.hole landing + bonus 186 (change p 186 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check489 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check490 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 .south p = true := by
  change ((!walkGuard soko1_2.board support p 212 238 .south || decide (bonus 212 p ≤ bonus 238 p)) && ((PreciseRolling.stayTargets soko1_2.board 238 .south).all (fun landing => !pushGuard support p 212 238 264 landing || decide (bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some landing)))) && (pushTargets soko1_2.board 238 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 212 238 264 landing || decide (bonus 212 p ≤ 1 - Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.hole landing + bonus 238 (change p 238 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check491 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check492 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 .east p = true := by
  change ((!walkGuard soko1_2.board support p 212 213 .east || decide (bonus 212 p ≤ bonus 213 p)) && ((PreciseRolling.stayTargets soko1_2.board 213 .east).all (fun landing => !pushGuard support p 212 213 214 landing || decide (bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some landing)))) && (pushTargets soko1_2.board 213 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 212 213 214 landing || decide (bonus 212 p ≤ 1 - Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.hole landing + bonus 213 (change p 213 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check493 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check494 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 .west p = true := by
  change ((!walkGuard soko1_2.board support p 212 211 .west || decide (bonus 212 p ≤ bonus 211 p)) && ((PreciseRolling.stayTargets soko1_2.board 211 .west).all (fun landing => !pushGuard support p 212 211 210 landing || decide (bonus 212 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some landing)))) && (pushTargets soko1_2.board 211 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 212 211 210 landing || decide (bonus 212 p ≤ 1 - Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.hole landing + bonus 211 (change p 211 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check495 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check496 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 212 187 .northEast || decide (bonus 212 p ≤ bonus 187 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check497 p, rfl⟩
theorem dir212_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 212 185 .northWest || decide (bonus 212 p ≤ bonus 185 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check498 p, rfl⟩
theorem dir212_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 212 239 .southEast || decide (bonus 212 p ≤ bonus 239 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check499 p, rfl⟩
theorem dir212_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 212 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 212 237 .southWest || decide (bonus 212 p ≤ bonus 237 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check500 p, rfl⟩
theorem dir213_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 .north p = true := by
  change ((!walkGuard soko1_2.board support p 213 187 .north || decide (bonus 213 p ≤ bonus 187 p)) && ((PreciseRolling.stayTargets soko1_2.board 187 .north).all (fun landing => !pushGuard support p 213 187 161 landing || decide (bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 187 + bonus 187 (change p 187 (some landing)))) && (pushTargets soko1_2.board 187 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 213 187 161 landing || decide (bonus 213 p ≤ 1 - Generated.soko1_2Potential.boulder 187 - Generated.soko1_2Potential.hole landing + bonus 187 (change p 187 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check501 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check502 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 .south p = true := by
  change ((!walkGuard soko1_2.board support p 213 239 .south || decide (bonus 213 p ≤ bonus 239 p)) && ((PreciseRolling.stayTargets soko1_2.board 239 .south).all (fun landing => !pushGuard support p 213 239 265 landing || decide (bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 239 + bonus 239 (change p 239 (some landing)))) && (pushTargets soko1_2.board 239 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 213 239 265 landing || decide (bonus 213 p ≤ 1 - Generated.soko1_2Potential.boulder 239 - Generated.soko1_2Potential.hole landing + bonus 239 (change p 239 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check503 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check504 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 .east p = true := by
  change ((!walkGuard soko1_2.board support p 213 214 .east || decide (bonus 213 p ≤ bonus 214 p)) && ((PreciseRolling.stayTargets soko1_2.board 214 .east).all (fun landing => !pushGuard support p 213 214 215 landing || decide (bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 214 + bonus 214 (change p 214 (some landing)))) && (pushTargets soko1_2.board 214 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 213 214 215 landing || decide (bonus 213 p ≤ 1 - Generated.soko1_2Potential.boulder 214 - Generated.soko1_2Potential.hole landing + bonus 214 (change p 214 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check505 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check506 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 .west p = true := by
  change ((!walkGuard soko1_2.board support p 213 212 .west || decide (bonus 213 p ≤ bonus 212 p)) && ((PreciseRolling.stayTargets soko1_2.board 212 .west).all (fun landing => !pushGuard support p 213 212 211 landing || decide (bonus 213 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some landing)))) && (pushTargets soko1_2.board 212 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 213 212 211 landing || decide (bonus 213 p ≤ 1 - Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.hole landing + bonus 212 (change p 212 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check507 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check508 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 .northEast p = true := by
  rfl
theorem dir213_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 213 186 .northWest || decide (bonus 213 p ≤ bonus 186 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check509 p, rfl⟩
theorem dir213_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 .southEast p = true := by
  rfl
theorem dir213_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 213 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 213 238 .southWest || decide (bonus 213 p ≤ bonus 238 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check510 p, rfl⟩
theorem dir214_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 .north p = true := by
  rfl
theorem dir214_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 .south p = true := by
  rfl
theorem dir214_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 .east p = true := by
  change ((!walkGuard soko1_2.board support p 214 215 .east || decide (bonus 214 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko1_2.board 215 .east).all (fun landing => !pushGuard support p 214 215 216 landing || decide (bonus 214 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko1_2.board 215 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 214 215 216 landing || decide (bonus 214 p ≤ 1 - Generated.soko1_2Potential.boulder 215 - Generated.soko1_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check511 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check512 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir214_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 .west p = true := by
  change ((!walkGuard soko1_2.board support p 214 213 .west || decide (bonus 214 p ≤ bonus 213 p)) && ((PreciseRolling.stayTargets soko1_2.board 213 .west).all (fun landing => !pushGuard support p 214 213 212 landing || decide (bonus 214 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some landing)))) && (pushTargets soko1_2.board 213 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 214 213 212 landing || decide (bonus 214 p ≤ 1 - Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.hole landing + bonus 213 (change p 213 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check513 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check514 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir214_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 214 189 .northEast || decide (bonus 214 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check515 p, rfl⟩
theorem dir214_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 214 187 .northWest || decide (bonus 214 p ≤ bonus 187 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check516 p, rfl⟩
theorem dir214_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 214 241 .southEast || decide (bonus 214 p ≤ bonus 241 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check517 p, rfl⟩
theorem dir214_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 214 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 214 239 .southWest || decide (bonus 214 p ≤ bonus 239 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check518 p, rfl⟩
end NetHack.Sokoban12CostPartition
