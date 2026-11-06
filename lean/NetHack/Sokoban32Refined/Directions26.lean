import NetHack.Sokoban32Refined.Directions25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir287_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 .north p = true := by
  change ((!walkGuard soko3_2.board support p 287 261 .north || decide (bonus 287 p ≤ bonus 261 p)) && ((PreciseRolling.stayTargets soko3_2.board 261 .north).all (fun landing => !pushGuard support p 287 261 235 landing || decide (bonus 287 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 261 + bonus 261 (change p 261 (some landing)))) && (pushTargets soko3_2.board 261 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 287 261 235 landing || decide (bonus 287 p ≤ 1 - Generated.soko3_2Potential.boulder 261 - Generated.soko3_2Potential.hole landing + bonus 261 (change p 261 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1265 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1266 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir287_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 .south p = true := by
  rfl
theorem dir287_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 .east p = true := by
  change ((!walkGuard soko3_2.board support p 287 288 .east || decide (bonus 287 p ≤ bonus 288 p)) && ((PreciseRolling.stayTargets soko3_2.board 288 .east).all (fun landing => !pushGuard support p 287 288 289 landing || decide (bonus 287 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 288 + bonus 288 (change p 288 (some landing)))) && (pushTargets soko3_2.board 288 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 287 288 289 landing || decide (bonus 287 p ≤ 1 - Generated.soko3_2Potential.boulder 288 - Generated.soko3_2Potential.hole landing + bonus 288 (change p 288 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1267 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1268 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir287_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 .west p = true := by
  rfl
theorem dir287_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 287 262 .northEast || decide (bonus 287 p ≤ bonus 262 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1269 p, rfl⟩
theorem dir287_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 .northWest p = true := by
  rfl
theorem dir287_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 .southEast p = true := by
  rfl
theorem dir287_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 287 .southWest p = true := by
  rfl
theorem dir288_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 .north p = true := by
  change ((!walkGuard soko3_2.board support p 288 262 .north || decide (bonus 288 p ≤ bonus 262 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1270 p, rfl⟩
theorem dir288_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 .south p = true := by
  rfl
theorem dir288_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 .east p = true := by
  change ((!walkGuard soko3_2.board support p 288 289 .east || decide (bonus 288 p ≤ bonus 289 p)) && ((PreciseRolling.stayTargets soko3_2.board 289 .east).all (fun landing => !pushGuard support p 288 289 290 landing || decide (bonus 288 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 289 + bonus 289 (change p 289 (some landing)))) && (pushTargets soko3_2.board 289 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 288 289 290 landing || decide (bonus 288 p ≤ 1 - Generated.soko3_2Potential.boulder 289 - Generated.soko3_2Potential.hole landing + bonus 289 (change p 289 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1271 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1272 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir288_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 .west p = true := by
  change ((!walkGuard soko3_2.board support p 288 287 .west || decide (bonus 288 p ≤ bonus 287 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1273 p, rfl⟩
theorem dir288_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 288 263 .northEast || decide (bonus 288 p ≤ bonus 263 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1274 p, rfl⟩
theorem dir288_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 288 261 .northWest || decide (bonus 288 p ≤ bonus 261 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1275 p, rfl⟩
theorem dir288_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 .southEast p = true := by
  rfl
theorem dir288_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 288 .southWest p = true := by
  rfl
theorem dir289_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 .north p = true := by
  change ((!walkGuard soko3_2.board support p 289 263 .north || decide (bonus 289 p ≤ bonus 263 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1276 p, rfl⟩
theorem dir289_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 .south p = true := by
  rfl
theorem dir289_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 .east p = true := by
  change ((!walkGuard soko3_2.board support p 289 290 .east || decide (bonus 289 p ≤ bonus 290 p)) && ((PreciseRolling.stayTargets soko3_2.board 290 .east).all (fun landing => !pushGuard support p 289 290 291 landing || decide (bonus 289 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 290 + bonus 290 (change p 290 (some landing)))) && (pushTargets soko3_2.board 290 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 289 290 291 landing || decide (bonus 289 p ≤ 1 - Generated.soko3_2Potential.boulder 290 - Generated.soko3_2Potential.hole landing + bonus 290 (change p 290 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1277 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1278 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir289_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 .west p = true := by
  change ((!walkGuard soko3_2.board support p 289 288 .west || decide (bonus 289 p ≤ bonus 288 p)) && ((PreciseRolling.stayTargets soko3_2.board 288 .west).all (fun landing => !pushGuard support p 289 288 287 landing || decide (bonus 289 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 288 + bonus 288 (change p 288 (some landing)))) && (pushTargets soko3_2.board 288 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 289 288 287 landing || decide (bonus 289 p ≤ 1 - Generated.soko3_2Potential.boulder 288 - Generated.soko3_2Potential.hole landing + bonus 288 (change p 288 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1279 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1280 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir289_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 .northEast p = true := by
  rfl
theorem dir289_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 289 262 .northWest || decide (bonus 289 p ≤ bonus 262 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1281 p, rfl⟩
theorem dir289_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 .southEast p = true := by
  rfl
theorem dir289_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 289 .southWest p = true := by
  rfl
theorem dir290_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 .north p = true := by
  rfl
theorem dir290_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 .south p = true := by
  rfl
theorem dir290_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 .east p = true := by
  change ((!walkGuard soko3_2.board support p 290 291 .east || decide (bonus 290 p ≤ bonus 291 p)) && ((PreciseRolling.stayTargets soko3_2.board 291 .east).all (fun landing => !pushGuard support p 290 291 292 landing || decide (bonus 290 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some landing)))) && (pushTargets soko3_2.board 291 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 290 291 292 landing || decide (bonus 290 p ≤ 1 - Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.hole landing + bonus 291 (change p 291 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1282 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1283 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir290_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 .west p = true := by
  change ((!walkGuard soko3_2.board support p 290 289 .west || decide (bonus 290 p ≤ bonus 289 p)) && ((PreciseRolling.stayTargets soko3_2.board 289 .west).all (fun landing => !pushGuard support p 290 289 288 landing || decide (bonus 290 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 289 + bonus 289 (change p 289 (some landing)))) && (pushTargets soko3_2.board 289 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 290 289 288 landing || decide (bonus 290 p ≤ 1 - Generated.soko3_2Potential.boulder 289 - Generated.soko3_2Potential.hole landing + bonus 289 (change p 289 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1284 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1285 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir290_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 290 265 .northEast || decide (bonus 290 p ≤ bonus 265 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1286 p, rfl⟩
theorem dir290_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 290 263 .northWest || decide (bonus 290 p ≤ bonus 263 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1287 p, rfl⟩
theorem dir290_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 290 317 .southEast || decide (bonus 290 p ≤ bonus 317 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1288 p, rfl⟩
theorem dir290_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 290 .southWest p = true := by
  rfl
theorem dir291_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 .north p = true := by
  change ((!walkGuard soko3_2.board support p 291 265 .north || decide (bonus 291 p ≤ bonus 265 p)) && ((PreciseRolling.stayTargets soko3_2.board 265 .north).all (fun landing => !pushGuard support p 291 265 239 landing || decide (bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 265 + bonus 265 (change p 265 (some landing)))) && (pushTargets soko3_2.board 265 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 291 265 239 landing || decide (bonus 291 p ≤ 1 - Generated.soko3_2Potential.boulder 265 - Generated.soko3_2Potential.hole landing + bonus 265 (change p 265 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1289 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1290 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir291_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 .south p = true := by
  change ((!walkGuard soko3_2.board support p 291 317 .south || decide (bonus 291 p ≤ bonus 317 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1291 p, rfl⟩
theorem dir291_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 .east p = true := by
  change ((!walkGuard soko3_2.board support p 291 292 .east || decide (bonus 291 p ≤ bonus 292 p)) && ((PreciseRolling.stayTargets soko3_2.board 292 .east).all (fun landing => !pushGuard support p 291 292 293 landing || decide (bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some landing)))) && (pushTargets soko3_2.board 292 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 291 292 293 landing || decide (bonus 291 p ≤ 1 - Generated.soko3_2Potential.boulder 292 - Generated.soko3_2Potential.hole landing + bonus 292 (change p 292 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1292 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1293 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir291_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 .west p = true := by
  change ((!walkGuard soko3_2.board support p 291 290 .west || decide (bonus 291 p ≤ bonus 290 p)) && ((PreciseRolling.stayTargets soko3_2.board 290 .west).all (fun landing => !pushGuard support p 291 290 289 landing || decide (bonus 291 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 290 + bonus 290 (change p 290 (some landing)))) && (pushTargets soko3_2.board 290 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 291 290 289 landing || decide (bonus 291 p ≤ 1 - Generated.soko3_2Potential.boulder 290 - Generated.soko3_2Potential.hole landing + bonus 290 (change p 290 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1294 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1295 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir291_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 291 266 .northEast || decide (bonus 291 p ≤ bonus 266 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1296 p, rfl⟩
theorem dir291_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 .northWest p = true := by
  rfl
theorem dir291_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 291 318 .southEast || decide (bonus 291 p ≤ bonus 318 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1297 p, rfl⟩
theorem dir291_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 291 .southWest p = true := by
  rfl
theorem dir292_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 .north p = true := by
  change ((!walkGuard soko3_2.board support p 292 266 .north || decide (bonus 292 p ≤ bonus 266 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1298 p, rfl⟩
theorem dir292_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 .south p = true := by
  change ((!walkGuard soko3_2.board support p 292 318 .south || decide (bonus 292 p ≤ bonus 318 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1299 p, rfl⟩
theorem dir292_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 .east p = true := by
  change ((!walkGuard soko3_2.board support p 292 293 .east || decide (bonus 292 p ≤ bonus 293 p)) && ((PreciseRolling.stayTargets soko3_2.board 293 .east).all (fun landing => !pushGuard support p 292 293 294 landing || decide (bonus 292 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 293 + bonus 293 (change p 293 (some landing)))) && (pushTargets soko3_2.board 293 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 292 293 294 landing || decide (bonus 292 p ≤ 1 - Generated.soko3_2Potential.boulder 293 - Generated.soko3_2Potential.hole landing + bonus 293 (change p 293 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1300 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1301 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir292_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 .west p = true := by
  change ((!walkGuard soko3_2.board support p 292 291 .west || decide (bonus 292 p ≤ bonus 291 p)) && ((PreciseRolling.stayTargets soko3_2.board 291 .west).all (fun landing => !pushGuard support p 292 291 290 landing || decide (bonus 292 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some landing)))) && (pushTargets soko3_2.board 291 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 292 291 290 landing || decide (bonus 292 p ≤ 1 - Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.hole landing + bonus 291 (change p 291 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1302 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1303 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir292_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 292 267 .northEast || decide (bonus 292 p ≤ bonus 267 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1304 p, rfl⟩
theorem dir292_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 292 265 .northWest || decide (bonus 292 p ≤ bonus 265 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1305 p, rfl⟩
theorem dir292_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 .southEast p = true := by
  rfl
theorem dir292_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 292 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 292 317 .southWest || decide (bonus 292 p ≤ bonus 317 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1306 p, rfl⟩
end NetHack.Sokoban32Refined
