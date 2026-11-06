import NetHack.Sokoban12CostPartition.Directions11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir215_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 .north p = true := by
  change ((!walkGuard soko1_2.board support p 215 189 .north || decide (bonus 215 p ≤ bonus 189 p)) && ((PreciseRolling.stayTargets soko1_2.board 189 .north).all (fun landing => !pushGuard support p 215 189 163 landing || decide (bonus 215 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 189 + bonus 189 (change p 189 (some landing)))) && (pushTargets soko1_2.board 189 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 215 189 163 landing || decide (bonus 215 p ≤ 1 - Generated.soko1_2Potential.boulder 189 - Generated.soko1_2Potential.hole landing + bonus 189 (change p 189 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check519 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check520 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir215_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 .south p = true := by
  change ((!walkGuard soko1_2.board support p 215 241 .south || decide (bonus 215 p ≤ bonus 241 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check521 p, rfl⟩
theorem dir215_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 .east p = true := by
  change ((!walkGuard soko1_2.board support p 215 216 .east || decide (bonus 215 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check522 p, rfl⟩
theorem dir215_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 .west p = true := by
  change ((!walkGuard soko1_2.board support p 215 214 .west || decide (bonus 215 p ≤ bonus 214 p)) && ((PreciseRolling.stayTargets soko1_2.board 214 .west).all (fun landing => !pushGuard support p 215 214 213 landing || decide (bonus 215 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 214 + bonus 214 (change p 214 (some landing)))) && (pushTargets soko1_2.board 214 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 215 214 213 landing || decide (bonus 215 p ≤ 1 - Generated.soko1_2Potential.boulder 214 - Generated.soko1_2Potential.hole landing + bonus 214 (change p 214 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check523 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check524 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir215_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 215 190 .northEast || decide (bonus 215 p ≤ bonus 190 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check525 p, rfl⟩
theorem dir215_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 .northWest p = true := by
  rfl
theorem dir215_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 215 242 .southEast || decide (bonus 215 p ≤ bonus 242 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check526 p, rfl⟩
theorem dir215_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 215 .southWest p = true := by
  rfl
theorem dir216_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 .north p = true := by
  change ((!walkGuard soko1_2.board support p 216 190 .north || decide (bonus 216 p ≤ bonus 190 p)) && ((PreciseRolling.stayTargets soko1_2.board 190 .north).all (fun landing => !pushGuard support p 216 190 164 landing || decide (bonus 216 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some landing)))) && (pushTargets soko1_2.board 190 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 216 190 164 landing || decide (bonus 216 p ≤ 1 - Generated.soko1_2Potential.boulder 190 - Generated.soko1_2Potential.hole landing + bonus 190 (change p 190 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check527 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check528 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir216_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 .south p = true := by
  change ((!walkGuard soko1_2.board support p 216 242 .south || decide (bonus 216 p ≤ bonus 242 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check529 p, rfl⟩
theorem dir216_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 .east p = true := by
  rfl
theorem dir216_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 .west p = true := by
  change ((!walkGuard soko1_2.board support p 216 215 .west || decide (bonus 216 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko1_2.board 215 .west).all (fun landing => !pushGuard support p 216 215 214 landing || decide (bonus 216 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko1_2.board 215 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 216 215 214 landing || decide (bonus 216 p ≤ 1 - Generated.soko1_2Potential.boulder 215 - Generated.soko1_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check530 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check531 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir216_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 216 191 .northEast || decide (bonus 216 p ≤ bonus 191 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check532 p, rfl⟩
theorem dir216_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 216 189 .northWest || decide (bonus 216 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check533 p, rfl⟩
theorem dir216_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 .southEast p = true := by
  rfl
theorem dir216_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 216 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 216 241 .southWest || decide (bonus 216 p ≤ bonus 241 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check534 p, rfl⟩
theorem dir218_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 .north p = true := by
  change ((!walkGuard soko1_2.board support p 218 192 .north || decide (bonus 218 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko1_2.board 192 .north).all (fun landing => !pushGuard support p 218 192 166 landing || decide (bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko1_2.board 192 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 218 192 166 landing || decide (bonus 218 p ≤ 1 - Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check535 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check536 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir218_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 .south p = true := by
  change ((!walkGuard soko1_2.board support p 218 244 .south || decide (bonus 218 p ≤ bonus 244 p)) && ((PreciseRolling.stayTargets soko1_2.board 244 .south).all (fun landing => !pushGuard support p 218 244 270 landing || decide (bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 244 + bonus 244 (change p 244 (some landing)))) && (pushTargets soko1_2.board 244 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 218 244 270 landing || decide (bonus 218 p ≤ 1 - Generated.soko1_2Potential.boulder 244 - Generated.soko1_2Potential.hole landing + bonus 244 (change p 244 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check537 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check538 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir218_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 .east p = true := by
  change ((!walkGuard soko1_2.board support p 218 219 .east || decide (bonus 218 p ≤ bonus 219 p)) && ((PreciseRolling.stayTargets soko1_2.board 219 .east).all (fun landing => !pushGuard support p 218 219 220 landing || decide (bonus 218 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some landing)))) && (pushTargets soko1_2.board 219 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 218 219 220 landing || decide (bonus 218 p ≤ 1 - Generated.soko1_2Potential.boulder 219 - Generated.soko1_2Potential.hole landing + bonus 219 (change p 219 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check539 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check540 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir218_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 .west p = true := by
  rfl
theorem dir218_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 218 193 .northEast || decide (bonus 218 p ≤ bonus 193 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check541 p, rfl⟩
theorem dir218_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 218 191 .northWest || decide (bonus 218 p ≤ bonus 191 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check542 p, rfl⟩
theorem dir218_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 218 245 .southEast || decide (bonus 218 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check543 p, rfl⟩
theorem dir218_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 218 .southWest p = true := by
  rfl
theorem dir219_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 .north p = true := by
  change ((!walkGuard soko1_2.board support p 219 193 .north || decide (bonus 219 p ≤ bonus 193 p)) && ((PreciseRolling.stayTargets soko1_2.board 193 .north).all (fun landing => !pushGuard support p 219 193 167 landing || decide (bonus 219 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some landing)))) && (pushTargets soko1_2.board 193 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 219 193 167 landing || decide (bonus 219 p ≤ 1 - Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.hole landing + bonus 193 (change p 193 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check544 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check545 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir219_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 .south p = true := by
  change ((!walkGuard soko1_2.board support p 219 245 .south || decide (bonus 219 p ≤ bonus 245 p)) && ((PreciseRolling.stayTargets soko1_2.board 245 .south).all (fun landing => !pushGuard support p 219 245 271 landing || decide (bonus 219 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 245 + bonus 245 (change p 245 (some landing)))) && (pushTargets soko1_2.board 245 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 219 245 271 landing || decide (bonus 219 p ≤ 1 - Generated.soko1_2Potential.boulder 245 - Generated.soko1_2Potential.hole landing + bonus 245 (change p 245 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check546 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check547 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir219_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 .east p = true := by
  change ((!walkGuard soko1_2.board support p 219 220 .east || decide (bonus 219 p ≤ bonus 220 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check548 p, rfl⟩
theorem dir219_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 .west p = true := by
  change ((!walkGuard soko1_2.board support p 219 218 .west || decide (bonus 219 p ≤ bonus 218 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check549 p, rfl⟩
theorem dir219_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 219 194 .northEast || decide (bonus 219 p ≤ bonus 194 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check550 p, rfl⟩
theorem dir219_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 219 192 .northWest || decide (bonus 219 p ≤ bonus 192 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check551 p, rfl⟩
theorem dir219_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 219 246 .southEast || decide (bonus 219 p ≤ bonus 246 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check552 p, rfl⟩
theorem dir219_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 219 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 219 244 .southWest || decide (bonus 219 p ≤ bonus 244 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check553 p, rfl⟩
theorem dir220_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 .north p = true := by
  change ((!walkGuard soko1_2.board support p 220 194 .north || decide (bonus 220 p ≤ bonus 194 p)) && ((PreciseRolling.stayTargets soko1_2.board 194 .north).all (fun landing => !pushGuard support p 220 194 168 landing || decide (bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 194 + bonus 194 (change p 194 (some landing)))) && (pushTargets soko1_2.board 194 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 220 194 168 landing || decide (bonus 220 p ≤ 1 - Generated.soko1_2Potential.boulder 194 - Generated.soko1_2Potential.hole landing + bonus 194 (change p 194 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check554 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check555 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir220_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 .south p = true := by
  change ((!walkGuard soko1_2.board support p 220 246 .south || decide (bonus 220 p ≤ bonus 246 p)) && ((PreciseRolling.stayTargets soko1_2.board 246 .south).all (fun landing => !pushGuard support p 220 246 272 landing || decide (bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 246 + bonus 246 (change p 246 (some landing)))) && (pushTargets soko1_2.board 246 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 220 246 272 landing || decide (bonus 220 p ≤ 1 - Generated.soko1_2Potential.boulder 246 - Generated.soko1_2Potential.hole landing + bonus 246 (change p 246 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check556 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check557 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir220_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 .east p = true := by
  rfl
theorem dir220_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 .west p = true := by
  change ((!walkGuard soko1_2.board support p 220 219 .west || decide (bonus 220 p ≤ bonus 219 p)) && ((PreciseRolling.stayTargets soko1_2.board 219 .west).all (fun landing => !pushGuard support p 220 219 218 landing || decide (bonus 220 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some landing)))) && (pushTargets soko1_2.board 219 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 220 219 218 landing || decide (bonus 220 p ≤ 1 - Generated.soko1_2Potential.boulder 219 - Generated.soko1_2Potential.hole landing + bonus 219 (change p 219 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check558 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check559 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir220_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 .northEast p = true := by
  rfl
theorem dir220_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 220 193 .northWest || decide (bonus 220 p ≤ bonus 193 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check560 p, rfl⟩
theorem dir220_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 .southEast p = true := by
  rfl
theorem dir220_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 220 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 220 245 .southWest || decide (bonus 220 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check561 p, rfl⟩
theorem dir232_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 .north p = true := by
  change ((!walkGuard soko1_2.board support p 232 206 .north || decide (bonus 232 p ≤ bonus 206 p)) && ((PreciseRolling.stayTargets soko1_2.board 206 .north).all (fun landing => !pushGuard support p 232 206 180 landing || decide (bonus 232 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 206 + bonus 206 (change p 206 (some landing)))) && (pushTargets soko1_2.board 206 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 232 206 180 landing || decide (bonus 232 p ≤ 1 - Generated.soko1_2Potential.boulder 206 - Generated.soko1_2Potential.hole landing + bonus 206 (change p 206 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check562 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check563 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir232_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 .south p = true := by
  change ((!walkGuard soko1_2.board support p 232 258 .south || decide (bonus 232 p ≤ bonus 258 p)) && ((PreciseRolling.stayTargets soko1_2.board 258 .south).all (fun landing => !pushGuard support p 232 258 284 landing || decide (bonus 232 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 258 + bonus 258 (change p 258 (some landing)))) && (pushTargets soko1_2.board 258 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 232 258 284 landing || decide (bonus 232 p ≤ 1 - Generated.soko1_2Potential.boulder 258 - Generated.soko1_2Potential.hole landing + bonus 258 (change p 258 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check564 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check565 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir232_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 .east p = true := by
  rfl
theorem dir232_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 .west p = true := by
  rfl
theorem dir232_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 .northEast p = true := by
  rfl
theorem dir232_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 .northWest p = true := by
  rfl
theorem dir232_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 .southEast p = true := by
  rfl
theorem dir232_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 232 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
