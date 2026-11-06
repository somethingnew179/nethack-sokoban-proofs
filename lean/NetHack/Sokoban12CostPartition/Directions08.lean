import NetHack.Sokoban12CostPartition.Directions07
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir161_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 .north p = true := by
  change ((!walkGuard soko1_2.board support p 161 135 .north || decide (bonus 161 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check317 p, rfl⟩
theorem dir161_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 .south p = true := by
  change ((!walkGuard soko1_2.board support p 161 187 .south || decide (bonus 161 p ≤ bonus 187 p)) && ((PreciseRolling.stayTargets soko1_2.board 187 .south).all (fun landing => !pushGuard support p 161 187 213 landing || decide (bonus 161 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 187 + bonus 187 (change p 187 (some landing)))) && (pushTargets soko1_2.board 187 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 161 187 213 landing || decide (bonus 161 p ≤ 1 - Generated.soko1_2Potential.boulder 187 - Generated.soko1_2Potential.hole landing + bonus 187 (change p 187 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check318 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check319 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir161_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 .east p = true := by
  rfl
theorem dir161_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 .west p = true := by
  change ((!walkGuard soko1_2.board support p 161 160 .west || decide (bonus 161 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko1_2.board 160 .west).all (fun landing => !pushGuard support p 161 160 159 landing || decide (bonus 161 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko1_2.board 160 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 161 160 159 landing || decide (bonus 161 p ≤ 1 - Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check320 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check321 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir161_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 .northEast p = true := by
  rfl
theorem dir161_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 161 134 .northWest || decide (bonus 161 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check322 p, rfl⟩
theorem dir161_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 .southEast p = true := by
  rfl
theorem dir161_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 161 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 161 186 .southWest || decide (bonus 161 p ≤ bonus 186 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check323 p, rfl⟩
theorem dir163_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 .north p = true := by
  rfl
theorem dir163_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 .south p = true := by
  change ((!walkGuard soko1_2.board support p 163 189 .south || decide (bonus 163 p ≤ bonus 189 p)) && ((PreciseRolling.stayTargets soko1_2.board 189 .south).all (fun landing => !pushGuard support p 163 189 215 landing || decide (bonus 163 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 189 + bonus 189 (change p 189 (some landing)))) && (pushTargets soko1_2.board 189 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 163 189 215 landing || decide (bonus 163 p ≤ 1 - Generated.soko1_2Potential.boulder 189 - Generated.soko1_2Potential.hole landing + bonus 189 (change p 189 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check324 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check325 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir163_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 .east p = true := by
  change ((!walkGuard soko1_2.board support p 163 164 .east || decide (bonus 163 p ≤ bonus 164 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check326 p, rfl⟩
theorem dir163_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 .west p = true := by
  rfl
theorem dir163_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 .northEast p = true := by
  rfl
theorem dir163_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 .northWest p = true := by
  rfl
theorem dir163_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 163 190 .southEast || decide (bonus 163 p ≤ bonus 190 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check327 p, rfl⟩
theorem dir163_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 163 .southWest p = true := by
  rfl
theorem dir164_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 .north p = true := by
  rfl
theorem dir164_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 .south p = true := by
  change ((!walkGuard soko1_2.board support p 164 190 .south || decide (bonus 164 p ≤ bonus 190 p)) && ((PreciseRolling.stayTargets soko1_2.board 190 .south).all (fun landing => !pushGuard support p 164 190 216 landing || decide (bonus 164 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 190 + bonus 190 (change p 190 (some landing)))) && (pushTargets soko1_2.board 190 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 164 190 216 landing || decide (bonus 164 p ≤ 1 - Generated.soko1_2Potential.boulder 190 - Generated.soko1_2Potential.hole landing + bonus 190 (change p 190 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check328 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check329 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir164_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 .east p = true := by
  rfl
theorem dir164_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 .west p = true := by
  change ((!walkGuard soko1_2.board support p 164 163 .west || decide (bonus 164 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check330 p, rfl⟩
theorem dir164_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 .northEast p = true := by
  rfl
theorem dir164_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 .northWest p = true := by
  rfl
theorem dir164_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 164 191 .southEast || decide (bonus 164 p ≤ bonus 191 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check331 p, rfl⟩
theorem dir164_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 164 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 164 189 .southWest || decide (bonus 164 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check332 p, rfl⟩
theorem dir166_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 .north p = true := by
  change ((!walkGuard soko1_2.board support p 166 140 .north || decide (bonus 166 p ≤ bonus 140 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check333 p, rfl⟩
theorem dir166_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 .south p = true := by
  change ((!walkGuard soko1_2.board support p 166 192 .south || decide (bonus 166 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko1_2.board 192 .south).all (fun landing => !pushGuard support p 166 192 218 landing || decide (bonus 166 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko1_2.board 192 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 166 192 218 landing || decide (bonus 166 p ≤ 1 - Generated.soko1_2Potential.boulder 192 - Generated.soko1_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check334 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check335 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir166_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 .east p = true := by
  change ((!walkGuard soko1_2.board support p 166 167 .east || decide (bonus 166 p ≤ bonus 167 p)) && ((PreciseRolling.stayTargets soko1_2.board 167 .east).all (fun landing => !pushGuard support p 166 167 168 landing || decide (bonus 166 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some landing)))) && (pushTargets soko1_2.board 167 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 166 167 168 landing || decide (bonus 166 p ≤ 1 - Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.hole landing + bonus 167 (change p 167 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check336 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check337 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir166_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 .west p = true := by
  rfl
theorem dir166_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 166 141 .northEast || decide (bonus 166 p ≤ bonus 141 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check338 p, rfl⟩
theorem dir166_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 .northWest p = true := by
  rfl
theorem dir166_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 166 193 .southEast || decide (bonus 166 p ≤ bonus 193 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check339 p, rfl⟩
theorem dir166_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 166 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 166 191 .southWest || decide (bonus 166 p ≤ bonus 191 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check340 p, rfl⟩
theorem dir167_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 .north p = true := by
  change ((!walkGuard soko1_2.board support p 167 141 .north || decide (bonus 167 p ≤ bonus 141 p)) && ((PreciseRolling.stayTargets soko1_2.board 141 .north).all (fun landing => !pushGuard support p 167 141 115 landing || decide (bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some landing)))) && (pushTargets soko1_2.board 141 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 167 141 115 landing || decide (bonus 167 p ≤ 1 - Generated.soko1_2Potential.boulder 141 - Generated.soko1_2Potential.hole landing + bonus 141 (change p 141 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check341 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check342 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir167_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 .south p = true := by
  change ((!walkGuard soko1_2.board support p 167 193 .south || decide (bonus 167 p ≤ bonus 193 p)) && ((PreciseRolling.stayTargets soko1_2.board 193 .south).all (fun landing => !pushGuard support p 167 193 219 landing || decide (bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 193 + bonus 193 (change p 193 (some landing)))) && (pushTargets soko1_2.board 193 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 167 193 219 landing || decide (bonus 167 p ≤ 1 - Generated.soko1_2Potential.boulder 193 - Generated.soko1_2Potential.hole landing + bonus 193 (change p 193 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check343 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check344 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir167_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 .east p = true := by
  change ((!walkGuard soko1_2.board support p 167 168 .east || decide (bonus 167 p ≤ bonus 168 p)) && ((PreciseRolling.stayTargets soko1_2.board 168 .east).all (fun landing => !pushGuard support p 167 168 169 landing || decide (bonus 167 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some landing)))) && (pushTargets soko1_2.board 168 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 167 168 169 landing || decide (bonus 167 p ≤ 1 - Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.hole landing + bonus 168 (change p 168 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check345 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check346 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir167_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 .west p = true := by
  change ((!walkGuard soko1_2.board support p 167 166 .west || decide (bonus 167 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check347 p, rfl⟩
theorem dir167_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 167 142 .northEast || decide (bonus 167 p ≤ bonus 142 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check348 p, rfl⟩
theorem dir167_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 167 140 .northWest || decide (bonus 167 p ≤ bonus 140 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check349 p, rfl⟩
theorem dir167_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 167 194 .southEast || decide (bonus 167 p ≤ bonus 194 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check350 p, rfl⟩
theorem dir167_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 167 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 167 192 .southWest || decide (bonus 167 p ≤ bonus 192 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check351 p, rfl⟩
theorem dir168_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 .north p = true := by
  change ((!walkGuard soko1_2.board support p 168 142 .north || decide (bonus 168 p ≤ bonus 142 p)) && ((PreciseRolling.stayTargets soko1_2.board 142 .north).all (fun landing => !pushGuard support p 168 142 116 landing || decide (bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some landing)))) && (pushTargets soko1_2.board 142 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 168 142 116 landing || decide (bonus 168 p ≤ 1 - Generated.soko1_2Potential.boulder 142 - Generated.soko1_2Potential.hole landing + bonus 142 (change p 142 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check352 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check353 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir168_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 .south p = true := by
  change ((!walkGuard soko1_2.board support p 168 194 .south || decide (bonus 168 p ≤ bonus 194 p)) && ((PreciseRolling.stayTargets soko1_2.board 194 .south).all (fun landing => !pushGuard support p 168 194 220 landing || decide (bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 194 + bonus 194 (change p 194 (some landing)))) && (pushTargets soko1_2.board 194 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 168 194 220 landing || decide (bonus 168 p ≤ 1 - Generated.soko1_2Potential.boulder 194 - Generated.soko1_2Potential.hole landing + bonus 194 (change p 194 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check354 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check355 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir168_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 .east p = true := by
  change ((!walkGuard soko1_2.board support p 168 169 .east || decide (bonus 168 p ≤ bonus 169 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check356 p, rfl⟩
theorem dir168_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 .west p = true := by
  change ((!walkGuard soko1_2.board support p 168 167 .west || decide (bonus 168 p ≤ bonus 167 p)) && ((PreciseRolling.stayTargets soko1_2.board 167 .west).all (fun landing => !pushGuard support p 168 167 166 landing || decide (bonus 168 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some landing)))) && (pushTargets soko1_2.board 167 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 168 167 166 landing || decide (bonus 168 p ≤ 1 - Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.hole landing + bonus 167 (change p 167 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check357 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check358 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir168_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 168 143 .northEast || decide (bonus 168 p ≤ bonus 143 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check359 p, rfl⟩
theorem dir168_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 168 141 .northWest || decide (bonus 168 p ≤ bonus 141 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check360 p, rfl⟩
theorem dir168_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 .southEast p = true := by
  rfl
theorem dir168_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 168 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 168 193 .southWest || decide (bonus 168 p ≤ bonus 193 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check361 p, rfl⟩
end NetHack.Sokoban12CostPartition
