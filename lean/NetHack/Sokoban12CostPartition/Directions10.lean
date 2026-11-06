import NetHack.Sokoban12CostPartition.Directions09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir189_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 .north p = true := by
  change ((!walkGuard soko1_2.board support p 189 163 .north || decide (bonus 189 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check412 p, rfl⟩
theorem dir189_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 .south p = true := by
  change ((!walkGuard soko1_2.board support p 189 215 .south || decide (bonus 189 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko1_2.board 215 .south).all (fun landing => !pushGuard support p 189 215 241 landing || decide (bonus 189 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko1_2.board 215 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 189 215 241 landing || decide (bonus 189 p ≤ 1 - Generated.soko1_2Potential.boulder 215 - Generated.soko1_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check413 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check414 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir189_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 .east p = true := by
  change ((!walkGuard soko1_2.board support p 189 190 .east || decide (bonus 189 p ≤ bonus 190 p)) && ((PreciseRolling.stayTargets soko1_2.board 190 .east).all (fun landing => !pushGuard support p 189 190 191 landing || decide (bonus 189 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some landing)))) && (pushTargets soko1_2.board 190 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 189 190 191 landing || decide (bonus 189 p ≤ 1 - Generated.soko1_2Potential.boulder 190 - Generated.soko1_2Potential.hole landing + bonus 190 (change p 190 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check415 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check416 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir189_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 .west p = true := by
  rfl
theorem dir189_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 189 164 .northEast || decide (bonus 189 p ≤ bonus 164 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check417 p, rfl⟩
theorem dir189_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 .northWest p = true := by
  rfl
theorem dir189_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 189 216 .southEast || decide (bonus 189 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check418 p, rfl⟩
theorem dir189_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 189 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 189 214 .southWest || decide (bonus 189 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check419 p, rfl⟩
theorem dir190_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 .north p = true := by
  change ((!walkGuard soko1_2.board support p 190 164 .north || decide (bonus 190 p ≤ bonus 164 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check420 p, rfl⟩
theorem dir190_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 .south p = true := by
  change ((!walkGuard soko1_2.board support p 190 216 .south || decide (bonus 190 p ≤ bonus 216 p)) && ((PreciseRolling.stayTargets soko1_2.board 216 .south).all (fun landing => !pushGuard support p 190 216 242 landing || decide (bonus 190 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 216 + bonus 216 (change p 216 (some landing)))) && (pushTargets soko1_2.board 216 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 190 216 242 landing || decide (bonus 190 p ≤ 1 - Generated.soko1_2Potential.boulder 216 - Generated.soko1_2Potential.hole landing + bonus 216 (change p 216 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check421 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check422 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir190_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 .east p = true := by
  change ((!walkGuard soko1_2.board support p 190 191 .east || decide (bonus 190 p ≤ bonus 191 p)) && ((PreciseRolling.stayTargets soko1_2.board 191 .east).all (fun landing => !pushGuard support p 190 191 192 landing || decide (bonus 190 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 191 + bonus 191 (change p 191 (some landing)))) && (pushTargets soko1_2.board 191 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 190 191 192 landing || decide (bonus 190 p ≤ 1 - Generated.soko1_2Potential.boulder 191 - Generated.soko1_2Potential.hole landing + bonus 191 (change p 191 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check423 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check424 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir190_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 .west p = true := by
  change ((!walkGuard soko1_2.board support p 190 189 .west || decide (bonus 190 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check425 p, rfl⟩
theorem dir190_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 .northEast p = true := by
  rfl
theorem dir190_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 190 163 .northWest || decide (bonus 190 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check426 p, rfl⟩
theorem dir190_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 .southEast p = true := by
  rfl
theorem dir190_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 190 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 190 215 .southWest || decide (bonus 190 p ≤ bonus 215 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check427 p, rfl⟩
theorem dir191_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 .north p = true := by
  rfl
theorem dir191_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 .south p = true := by
  rfl
theorem dir191_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 .east p = true := by
  change ((!walkGuard soko1_2.board support p 191 192 .east || decide (bonus 191 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko1_2.board 192 .east).all (fun landing => !pushGuard support p 191 192 193 landing || decide (bonus 191 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko1_2.board 192 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 191 192 193 landing || decide (bonus 191 p ≤ 1 - Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check428 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check429 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir191_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 .west p = true := by
  change ((!walkGuard soko1_2.board support p 191 190 .west || decide (bonus 191 p ≤ bonus 190 p)) && ((PreciseRolling.stayTargets soko1_2.board 190 .west).all (fun landing => !pushGuard support p 191 190 189 landing || decide (bonus 191 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some landing)))) && (pushTargets soko1_2.board 190 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 191 190 189 landing || decide (bonus 191 p ≤ 1 - Generated.soko1_2Potential.boulder 190 - Generated.soko1_2Potential.hole landing + bonus 190 (change p 190 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check430 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check431 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir191_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 191 166 .northEast || decide (bonus 191 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check432 p, rfl⟩
theorem dir191_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 191 164 .northWest || decide (bonus 191 p ≤ bonus 164 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check433 p, rfl⟩
theorem dir191_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 191 218 .southEast || decide (bonus 191 p ≤ bonus 218 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check434 p, rfl⟩
theorem dir191_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 191 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 191 216 .southWest || decide (bonus 191 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check435 p, rfl⟩
theorem dir192_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 .north p = true := by
  change ((!walkGuard soko1_2.board support p 192 166 .north || decide (bonus 192 p ≤ bonus 166 p)) && ((PreciseRolling.stayTargets soko1_2.board 166 .north).all (fun landing => !pushGuard support p 192 166 140 landing || decide (bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 166 + bonus 166 (change p 166 (some landing)))) && (pushTargets soko1_2.board 166 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 192 166 140 landing || decide (bonus 192 p ≤ 1 - Generated.soko1_2Potential.boulder 166 - Generated.soko1_2Potential.hole landing + bonus 166 (change p 166 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check436 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check437 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir192_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 .south p = true := by
  change ((!walkGuard soko1_2.board support p 192 218 .south || decide (bonus 192 p ≤ bonus 218 p)) && ((PreciseRolling.stayTargets soko1_2.board 218 .south).all (fun landing => !pushGuard support p 192 218 244 landing || decide (bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 218 + bonus 218 (change p 218 (some landing)))) && (pushTargets soko1_2.board 218 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 192 218 244 landing || decide (bonus 192 p ≤ 1 - Generated.soko1_2Potential.boulder 218 - Generated.soko1_2Potential.hole landing + bonus 218 (change p 218 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check438 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check439 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir192_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 .east p = true := by
  change ((!walkGuard soko1_2.board support p 192 193 .east || decide (bonus 192 p ≤ bonus 193 p)) && ((PreciseRolling.stayTargets soko1_2.board 193 .east).all (fun landing => !pushGuard support p 192 193 194 landing || decide (bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some landing)))) && (pushTargets soko1_2.board 193 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 192 193 194 landing || decide (bonus 192 p ≤ 1 - Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.hole landing + bonus 193 (change p 193 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check440 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check441 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir192_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 .west p = true := by
  change ((!walkGuard soko1_2.board support p 192 191 .west || decide (bonus 192 p ≤ bonus 191 p)) && ((PreciseRolling.stayTargets soko1_2.board 191 .west).all (fun landing => !pushGuard support p 192 191 190 landing || decide (bonus 192 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 191 + bonus 191 (change p 191 (some landing)))) && (pushTargets soko1_2.board 191 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 192 191 190 landing || decide (bonus 192 p ≤ 1 - Generated.soko1_2Potential.boulder 191 - Generated.soko1_2Potential.hole landing + bonus 191 (change p 191 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check442 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check443 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir192_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 192 167 .northEast || decide (bonus 192 p ≤ bonus 167 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check444 p, rfl⟩
theorem dir192_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 .northWest p = true := by
  rfl
theorem dir192_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 192 219 .southEast || decide (bonus 192 p ≤ bonus 219 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check445 p, rfl⟩
theorem dir192_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 192 .southWest p = true := by
  rfl
theorem dir193_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 .north p = true := by
  change ((!walkGuard soko1_2.board support p 193 167 .north || decide (bonus 193 p ≤ bonus 167 p)) && ((PreciseRolling.stayTargets soko1_2.board 167 .north).all (fun landing => !pushGuard support p 193 167 141 landing || decide (bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some landing)))) && (pushTargets soko1_2.board 167 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 193 167 141 landing || decide (bonus 193 p ≤ 1 - Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.hole landing + bonus 167 (change p 167 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check446 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check447 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir193_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 .south p = true := by
  change ((!walkGuard soko1_2.board support p 193 219 .south || decide (bonus 193 p ≤ bonus 219 p)) && ((PreciseRolling.stayTargets soko1_2.board 219 .south).all (fun landing => !pushGuard support p 193 219 245 landing || decide (bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 219 + bonus 219 (change p 219 (some landing)))) && (pushTargets soko1_2.board 219 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 193 219 245 landing || decide (bonus 193 p ≤ 1 - Generated.soko1_2Potential.boulder 219 - Generated.soko1_2Potential.hole landing + bonus 219 (change p 219 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check448 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check449 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir193_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 .east p = true := by
  change ((!walkGuard soko1_2.board support p 193 194 .east || decide (bonus 193 p ≤ bonus 194 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check450 p, rfl⟩
theorem dir193_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 .west p = true := by
  change ((!walkGuard soko1_2.board support p 193 192 .west || decide (bonus 193 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko1_2.board 192 .west).all (fun landing => !pushGuard support p 193 192 191 landing || decide (bonus 193 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko1_2.board 192 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 193 192 191 landing || decide (bonus 193 p ≤ 1 - Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check451 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check452 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir193_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 193 168 .northEast || decide (bonus 193 p ≤ bonus 168 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check453 p, rfl⟩
theorem dir193_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 193 166 .northWest || decide (bonus 193 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check454 p, rfl⟩
theorem dir193_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 193 220 .southEast || decide (bonus 193 p ≤ bonus 220 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check455 p, rfl⟩
theorem dir193_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 193 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 193 218 .southWest || decide (bonus 193 p ≤ bonus 218 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check456 p, rfl⟩
theorem dir194_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 .north p = true := by
  change ((!walkGuard soko1_2.board support p 194 168 .north || decide (bonus 194 p ≤ bonus 168 p)) && ((PreciseRolling.stayTargets soko1_2.board 168 .north).all (fun landing => !pushGuard support p 194 168 142 landing || decide (bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some landing)))) && (pushTargets soko1_2.board 168 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 194 168 142 landing || decide (bonus 194 p ≤ 1 - Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.hole landing + bonus 168 (change p 168 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check457 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check458 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir194_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 .south p = true := by
  change ((!walkGuard soko1_2.board support p 194 220 .south || decide (bonus 194 p ≤ bonus 220 p)) && ((PreciseRolling.stayTargets soko1_2.board 220 .south).all (fun landing => !pushGuard support p 194 220 246 landing || decide (bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 220 + bonus 220 (change p 220 (some landing)))) && (pushTargets soko1_2.board 220 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 194 220 246 landing || decide (bonus 194 p ≤ 1 - Generated.soko1_2Potential.boulder 220 - Generated.soko1_2Potential.hole landing + bonus 220 (change p 220 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check459 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check460 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir194_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 .east p = true := by
  rfl
theorem dir194_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 .west p = true := by
  change ((!walkGuard soko1_2.board support p 194 193 .west || decide (bonus 194 p ≤ bonus 193 p)) && ((PreciseRolling.stayTargets soko1_2.board 193 .west).all (fun landing => !pushGuard support p 194 193 192 landing || decide (bonus 194 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some landing)))) && (pushTargets soko1_2.board 193 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 194 193 192 landing || decide (bonus 194 p ≤ 1 - Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.hole landing + bonus 193 (change p 193 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check461 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check462 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir194_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 194 169 .northEast || decide (bonus 194 p ≤ bonus 169 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check463 p, rfl⟩
theorem dir194_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 194 167 .northWest || decide (bonus 194 p ≤ bonus 167 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check464 p, rfl⟩
theorem dir194_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 .southEast p = true := by
  rfl
theorem dir194_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 194 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 194 219 .southWest || decide (bonus 194 p ≤ bonus 219 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check465 p, rfl⟩
end NetHack.Sokoban12CostPartition
