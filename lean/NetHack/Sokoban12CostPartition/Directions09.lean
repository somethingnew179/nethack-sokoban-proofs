import NetHack.Sokoban12CostPartition.Directions08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir169_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 .north p = true := by
  change ((!walkGuard soko1_2.board support p 169 143 .north || decide (bonus 169 p ≤ bonus 143 p)) && ((PreciseRolling.stayTargets soko1_2.board 143 .north).all (fun landing => !pushGuard support p 169 143 117 landing || decide (bonus 169 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 143 + bonus 143 (change p 143 (some landing)))) && (pushTargets soko1_2.board 143 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 169 143 117 landing || decide (bonus 169 p ≤ 1 - Generated.soko1_2Potential.boulder 143 - Generated.soko1_2Potential.hole landing + bonus 143 (change p 143 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check362 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check363 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir169_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 .south p = true := by
  rfl
theorem dir169_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 .east p = true := by
  rfl
theorem dir169_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 .west p = true := by
  change ((!walkGuard soko1_2.board support p 169 168 .west || decide (bonus 169 p ≤ bonus 168 p)) && ((PreciseRolling.stayTargets soko1_2.board 168 .west).all (fun landing => !pushGuard support p 169 168 167 landing || decide (bonus 169 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some landing)))) && (pushTargets soko1_2.board 168 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 169 168 167 landing || decide (bonus 169 p ≤ 1 - Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.hole landing + bonus 168 (change p 168 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check364 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check365 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir169_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 .northEast p = true := by
  rfl
theorem dir169_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 169 142 .northWest || decide (bonus 169 p ≤ bonus 142 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check366 p, rfl⟩
theorem dir169_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 .southEast p = true := by
  rfl
theorem dir169_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 169 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 169 194 .southWest || decide (bonus 169 p ≤ bonus 194 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check367 p, rfl⟩
theorem dir180_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 .north p = true := by
  change ((!walkGuard soko1_2.board support p 180 154 .north || decide (bonus 180 p ≤ bonus 154 p)) && ((PreciseRolling.stayTargets soko1_2.board 154 .north).all (fun landing => !pushGuard support p 180 154 128 landing || decide (bonus 180 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 154 + bonus 154 (change p 154 (some landing)))) && (pushTargets soko1_2.board 154 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 180 154 128 landing || decide (bonus 180 p ≤ 1 - Generated.soko1_2Potential.boulder 154 - Generated.soko1_2Potential.hole landing + bonus 154 (change p 154 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check368 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check369 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir180_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 .south p = true := by
  change ((!walkGuard soko1_2.board support p 180 206 .south || decide (bonus 180 p ≤ bonus 206 p)) && ((PreciseRolling.stayTargets soko1_2.board 206 .south).all (fun landing => !pushGuard support p 180 206 232 landing || decide (bonus 180 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 206 + bonus 206 (change p 206 (some landing)))) && (pushTargets soko1_2.board 206 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 180 206 232 landing || decide (bonus 180 p ≤ 1 - Generated.soko1_2Potential.boulder 206 - Generated.soko1_2Potential.hole landing + bonus 206 (change p 206 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check370 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check371 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir180_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 .east p = true := by
  rfl
theorem dir180_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 .west p = true := by
  rfl
theorem dir180_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 .northEast p = true := by
  rfl
theorem dir180_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 .northWest p = true := by
  rfl
theorem dir180_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 .southEast p = true := by
  rfl
theorem dir180_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 180 .southWest p = true := by
  rfl
theorem dir184_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 .north p = true := by
  change ((!walkGuard soko1_2.board support p 184 158 .north || decide (bonus 184 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko1_2.board 158 .north).all (fun landing => !pushGuard support p 184 158 132 landing || decide (bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko1_2.board 158 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 184 158 132 landing || decide (bonus 184 p ≤ 1 - Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check372 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check373 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir184_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 .south p = true := by
  change ((!walkGuard soko1_2.board support p 184 210 .south || decide (bonus 184 p ≤ bonus 210 p)) && ((PreciseRolling.stayTargets soko1_2.board 210 .south).all (fun landing => !pushGuard support p 184 210 236 landing || decide (bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 210 + bonus 210 (change p 210 (some landing)))) && (pushTargets soko1_2.board 210 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 184 210 236 landing || decide (bonus 184 p ≤ 1 - Generated.soko1_2Potential.boulder 210 - Generated.soko1_2Potential.hole landing + bonus 210 (change p 210 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check374 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check375 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir184_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 .east p = true := by
  change ((!walkGuard soko1_2.board support p 184 185 .east || decide (bonus 184 p ≤ bonus 185 p)) && ((PreciseRolling.stayTargets soko1_2.board 185 .east).all (fun landing => !pushGuard support p 184 185 186 landing || decide (bonus 184 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some landing)))) && (pushTargets soko1_2.board 185 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 184 185 186 landing || decide (bonus 184 p ≤ 1 - Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.hole landing + bonus 185 (change p 185 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check376 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check377 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir184_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 .west p = true := by
  rfl
theorem dir184_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 184 159 .northEast || decide (bonus 184 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check378 p, rfl⟩
theorem dir184_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 184 157 .northWest || decide (bonus 184 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check379 p, rfl⟩
theorem dir184_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 184 211 .southEast || decide (bonus 184 p ≤ bonus 211 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check380 p, rfl⟩
theorem dir184_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 184 .southWest p = true := by
  rfl
theorem dir185_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 .north p = true := by
  change ((!walkGuard soko1_2.board support p 185 159 .north || decide (bonus 185 p ≤ bonus 159 p)) && ((PreciseRolling.stayTargets soko1_2.board 159 .north).all (fun landing => !pushGuard support p 185 159 133 landing || decide (bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some landing)))) && (pushTargets soko1_2.board 159 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 185 159 133 landing || decide (bonus 185 p ≤ 1 - Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.hole landing + bonus 159 (change p 159 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check381 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check382 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir185_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 .south p = true := by
  change ((!walkGuard soko1_2.board support p 185 211 .south || decide (bonus 185 p ≤ bonus 211 p)) && ((PreciseRolling.stayTargets soko1_2.board 211 .south).all (fun landing => !pushGuard support p 185 211 237 landing || decide (bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 211 + bonus 211 (change p 211 (some landing)))) && (pushTargets soko1_2.board 211 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 185 211 237 landing || decide (bonus 185 p ≤ 1 - Generated.soko1_2Potential.boulder 211 - Generated.soko1_2Potential.hole landing + bonus 211 (change p 211 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check383 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check384 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir185_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 .east p = true := by
  change ((!walkGuard soko1_2.board support p 185 186 .east || decide (bonus 185 p ≤ bonus 186 p)) && ((PreciseRolling.stayTargets soko1_2.board 186 .east).all (fun landing => !pushGuard support p 185 186 187 landing || decide (bonus 185 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some landing)))) && (pushTargets soko1_2.board 186 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 185 186 187 landing || decide (bonus 185 p ≤ 1 - Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.hole landing + bonus 186 (change p 186 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check385 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check386 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir185_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 .west p = true := by
  change ((!walkGuard soko1_2.board support p 185 184 .west || decide (bonus 185 p ≤ bonus 184 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check387 p, rfl⟩
theorem dir185_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 185 160 .northEast || decide (bonus 185 p ≤ bonus 160 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check388 p, rfl⟩
theorem dir185_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 185 158 .northWest || decide (bonus 185 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check389 p, rfl⟩
theorem dir185_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 185 212 .southEast || decide (bonus 185 p ≤ bonus 212 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check390 p, rfl⟩
theorem dir185_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 185 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 185 210 .southWest || decide (bonus 185 p ≤ bonus 210 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check391 p, rfl⟩
theorem dir186_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 .north p = true := by
  change ((!walkGuard soko1_2.board support p 186 160 .north || decide (bonus 186 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko1_2.board 160 .north).all (fun landing => !pushGuard support p 186 160 134 landing || decide (bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko1_2.board 160 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 186 160 134 landing || decide (bonus 186 p ≤ 1 - Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check392 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check393 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir186_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 .south p = true := by
  change ((!walkGuard soko1_2.board support p 186 212 .south || decide (bonus 186 p ≤ bonus 212 p)) && ((PreciseRolling.stayTargets soko1_2.board 212 .south).all (fun landing => !pushGuard support p 186 212 238 landing || decide (bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 212 + bonus 212 (change p 212 (some landing)))) && (pushTargets soko1_2.board 212 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 186 212 238 landing || decide (bonus 186 p ≤ 1 - Generated.soko1_2Potential.boulder 212 - Generated.soko1_2Potential.hole landing + bonus 212 (change p 212 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check394 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check395 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir186_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 .east p = true := by
  change ((!walkGuard soko1_2.board support p 186 187 .east || decide (bonus 186 p ≤ bonus 187 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check396 p, rfl⟩
theorem dir186_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 .west p = true := by
  change ((!walkGuard soko1_2.board support p 186 185 .west || decide (bonus 186 p ≤ bonus 185 p)) && ((PreciseRolling.stayTargets soko1_2.board 185 .west).all (fun landing => !pushGuard support p 186 185 184 landing || decide (bonus 186 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some landing)))) && (pushTargets soko1_2.board 185 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 186 185 184 landing || decide (bonus 186 p ≤ 1 - Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.hole landing + bonus 185 (change p 185 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check397 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check398 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir186_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 186 161 .northEast || decide (bonus 186 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check399 p, rfl⟩
theorem dir186_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 186 159 .northWest || decide (bonus 186 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check400 p, rfl⟩
theorem dir186_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 186 213 .southEast || decide (bonus 186 p ≤ bonus 213 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check401 p, rfl⟩
theorem dir186_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 186 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 186 211 .southWest || decide (bonus 186 p ≤ bonus 211 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check402 p, rfl⟩
theorem dir187_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 .north p = true := by
  change ((!walkGuard soko1_2.board support p 187 161 .north || decide (bonus 187 p ≤ bonus 161 p)) && ((PreciseRolling.stayTargets soko1_2.board 161 .north).all (fun landing => !pushGuard support p 187 161 135 landing || decide (bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 161 + bonus 161 (change p 161 (some landing)))) && (pushTargets soko1_2.board 161 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 187 161 135 landing || decide (bonus 187 p ≤ 1 - Generated.soko1_2Potential.boulder 161 - Generated.soko1_2Potential.hole landing + bonus 161 (change p 161 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check403 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check404 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir187_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 .south p = true := by
  change ((!walkGuard soko1_2.board support p 187 213 .south || decide (bonus 187 p ≤ bonus 213 p)) && ((PreciseRolling.stayTargets soko1_2.board 213 .south).all (fun landing => !pushGuard support p 187 213 239 landing || decide (bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 213 + bonus 213 (change p 213 (some landing)))) && (pushTargets soko1_2.board 213 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 187 213 239 landing || decide (bonus 187 p ≤ 1 - Generated.soko1_2Potential.boulder 213 - Generated.soko1_2Potential.hole landing + bonus 213 (change p 213 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check405 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check406 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir187_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 .east p = true := by
  rfl
theorem dir187_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 .west p = true := by
  change ((!walkGuard soko1_2.board support p 187 186 .west || decide (bonus 187 p ≤ bonus 186 p)) && ((PreciseRolling.stayTargets soko1_2.board 186 .west).all (fun landing => !pushGuard support p 187 186 185 landing || decide (bonus 187 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some landing)))) && (pushTargets soko1_2.board 186 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 187 186 185 landing || decide (bonus 187 p ≤ 1 - Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.hole landing + bonus 186 (change p 186 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check407 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check408 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir187_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 .northEast p = true := by
  rfl
theorem dir187_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 187 160 .northWest || decide (bonus 187 p ≤ bonus 160 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check409 p, rfl⟩
theorem dir187_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 187 214 .southEast || decide (bonus 187 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check410 p, rfl⟩
theorem dir187_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 187 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 187 212 .southWest || decide (bonus 187 p ≤ bonus 212 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check411 p, rfl⟩
end NetHack.Sokoban12CostPartition
