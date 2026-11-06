import NetHack.Sokoban32Refined.Directions26
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir293_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 .north p = true := by
  change ((!walkGuard soko3_2.board support p 293 267 .north || decide (bonus 293 p ≤ bonus 267 p)) && ((PreciseRolling.stayTargets soko3_2.board 267 .north).all (fun landing => !pushGuard support p 293 267 241 landing || decide (bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 267 + bonus 267 (change p 267 (some landing)))) && (pushTargets soko3_2.board 267 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 293 267 241 landing || decide (bonus 293 p ≤ 1 - Generated.soko3_2Potential.boulder 267 - Generated.soko3_2Potential.hole landing + bonus 267 (change p 267 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1307 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1308 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir293_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 .south p = true := by
  rfl
theorem dir293_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 .east p = true := by
  change ((!walkGuard soko3_2.board support p 293 294 .east || decide (bonus 293 p ≤ bonus 294 p)) && ((PreciseRolling.stayTargets soko3_2.board 294 .east).all (fun landing => !pushGuard support p 293 294 295 landing || decide (bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 294 + bonus 294 (change p 294 (some landing)))) && (pushTargets soko3_2.board 294 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 293 294 295 landing || decide (bonus 293 p ≤ 1 - Generated.soko3_2Potential.boulder 294 - Generated.soko3_2Potential.hole landing + bonus 294 (change p 294 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1309 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1310 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir293_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 .west p = true := by
  change ((!walkGuard soko3_2.board support p 293 292 .west || decide (bonus 293 p ≤ bonus 292 p)) && ((PreciseRolling.stayTargets soko3_2.board 292 .west).all (fun landing => !pushGuard support p 293 292 291 landing || decide (bonus 293 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some landing)))) && (pushTargets soko3_2.board 292 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 293 292 291 landing || decide (bonus 293 p ≤ 1 - Generated.soko3_2Potential.boulder 292 - Generated.soko3_2Potential.hole landing + bonus 292 (change p 292 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1311 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1312 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir293_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 .northEast p = true := by
  rfl
theorem dir293_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 293 266 .northWest || decide (bonus 293 p ≤ bonus 266 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1313 p, rfl⟩
theorem dir293_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 293 320 .southEast || decide (bonus 293 p ≤ bonus 320 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1314 p, rfl⟩
theorem dir293_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 293 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 293 318 .southWest || decide (bonus 293 p ≤ bonus 318 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1315 p, rfl⟩
theorem dir294_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 .north p = true := by
  rfl
theorem dir294_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 .south p = true := by
  change ((!walkGuard soko3_2.board support p 294 320 .south || decide (bonus 294 p ≤ bonus 320 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1316 p, rfl⟩
theorem dir294_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 .east p = true := by
  change ((!walkGuard soko3_2.board support p 294 295 .east || decide (bonus 294 p ≤ bonus 295 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1317 p, rfl⟩
theorem dir294_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 .west p = true := by
  change ((!walkGuard soko3_2.board support p 294 293 .west || decide (bonus 294 p ≤ bonus 293 p)) && ((PreciseRolling.stayTargets soko3_2.board 293 .west).all (fun landing => !pushGuard support p 294 293 292 landing || decide (bonus 294 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 293 + bonus 293 (change p 293 (some landing)))) && (pushTargets soko3_2.board 293 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 294 293 292 landing || decide (bonus 294 p ≤ 1 - Generated.soko3_2Potential.boulder 293 - Generated.soko3_2Potential.hole landing + bonus 293 (change p 293 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1318 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1319 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir294_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 294 269 .northEast || decide (bonus 294 p ≤ bonus 269 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1320 p, rfl⟩
theorem dir294_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 294 267 .northWest || decide (bonus 294 p ≤ bonus 267 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1321 p, rfl⟩
theorem dir294_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 294 321 .southEast || decide (bonus 294 p ≤ bonus 321 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1322 p, rfl⟩
theorem dir294_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 294 .southWest p = true := by
  rfl
theorem dir295_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 .north p = true := by
  change ((!walkGuard soko3_2.board support p 295 269 .north || decide (bonus 295 p ≤ bonus 269 p)) && ((PreciseRolling.stayTargets soko3_2.board 269 .north).all (fun landing => !pushGuard support p 295 269 243 landing || decide (bonus 295 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 269 + bonus 269 (change p 269 (some landing)))) && (pushTargets soko3_2.board 269 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 295 269 243 landing || decide (bonus 295 p ≤ 1 - Generated.soko3_2Potential.boulder 269 - Generated.soko3_2Potential.hole landing + bonus 269 (change p 269 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1323 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1324 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir295_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 .south p = true := by
  change ((!walkGuard soko3_2.board support p 295 321 .south || decide (bonus 295 p ≤ bonus 321 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1325 p, rfl⟩
theorem dir295_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 .east p = true := by
  rfl
theorem dir295_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 .west p = true := by
  change ((!walkGuard soko3_2.board support p 295 294 .west || decide (bonus 295 p ≤ bonus 294 p)) && ((PreciseRolling.stayTargets soko3_2.board 294 .west).all (fun landing => !pushGuard support p 295 294 293 landing || decide (bonus 295 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 294 + bonus 294 (change p 294 (some landing)))) && (pushTargets soko3_2.board 294 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 295 294 293 landing || decide (bonus 295 p ≤ 1 - Generated.soko3_2Potential.boulder 294 - Generated.soko3_2Potential.hole landing + bonus 294 (change p 294 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1326 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1327 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir295_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 295 270 .northEast || decide (bonus 295 p ≤ bonus 270 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1328 p, rfl⟩
theorem dir295_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 .northWest p = true := by
  rfl
theorem dir295_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 .southEast p = true := by
  rfl
theorem dir295_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 295 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 295 320 .southWest || decide (bonus 295 p ≤ bonus 320 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1329 p, rfl⟩
theorem dir317_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 .north p = true := by
  change ((!walkGuard soko3_2.board support p 317 291 .north || decide (bonus 317 p ≤ bonus 291 p)) && ((PreciseRolling.stayTargets soko3_2.board 291 .north).all (fun landing => !pushGuard support p 317 291 265 landing || decide (bonus 317 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some landing)))) && (pushTargets soko3_2.board 291 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 317 291 265 landing || decide (bonus 317 p ≤ 1 - Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.hole landing + bonus 291 (change p 291 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1330 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1331 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir317_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 .south p = true := by
  rfl
theorem dir317_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 .east p = true := by
  change ((!walkGuard soko3_2.board support p 317 318 .east || decide (bonus 317 p ≤ bonus 318 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1332 p, rfl⟩
theorem dir317_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 .west p = true := by
  rfl
theorem dir317_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 317 292 .northEast || decide (bonus 317 p ≤ bonus 292 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1333 p, rfl⟩
theorem dir317_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 317 290 .northWest || decide (bonus 317 p ≤ bonus 290 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1334 p, rfl⟩
theorem dir317_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 .southEast p = true := by
  rfl
theorem dir317_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 317 .southWest p = true := by
  rfl
theorem dir318_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 .north p = true := by
  change ((!walkGuard soko3_2.board support p 318 292 .north || decide (bonus 318 p ≤ bonus 292 p)) && ((PreciseRolling.stayTargets soko3_2.board 292 .north).all (fun landing => !pushGuard support p 318 292 266 landing || decide (bonus 318 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some landing)))) && (pushTargets soko3_2.board 292 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 318 292 266 landing || decide (bonus 318 p ≤ 1 - Generated.soko3_2Potential.boulder 292 - Generated.soko3_2Potential.hole landing + bonus 292 (change p 292 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1335 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1336 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir318_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 .south p = true := by
  rfl
theorem dir318_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 .east p = true := by
  rfl
theorem dir318_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 .west p = true := by
  change ((!walkGuard soko3_2.board support p 318 317 .west || decide (bonus 318 p ≤ bonus 317 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1337 p, rfl⟩
theorem dir318_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 318 293 .northEast || decide (bonus 318 p ≤ bonus 293 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1338 p, rfl⟩
theorem dir318_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 318 291 .northWest || decide (bonus 318 p ≤ bonus 291 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1339 p, rfl⟩
theorem dir318_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 .southEast p = true := by
  rfl
theorem dir318_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 318 .southWest p = true := by
  rfl
theorem dir320_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 .north p = true := by
  change ((!walkGuard soko3_2.board support p 320 294 .north || decide (bonus 320 p ≤ bonus 294 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1340 p, rfl⟩
theorem dir320_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 .south p = true := by
  rfl
theorem dir320_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 .east p = true := by
  change ((!walkGuard soko3_2.board support p 320 321 .east || decide (bonus 320 p ≤ bonus 321 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1341 p, rfl⟩
theorem dir320_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 .west p = true := by
  rfl
theorem dir320_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 320 295 .northEast || decide (bonus 320 p ≤ bonus 295 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1342 p, rfl⟩
theorem dir320_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 320 293 .northWest || decide (bonus 320 p ≤ bonus 293 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1343 p, rfl⟩
theorem dir320_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 .southEast p = true := by
  rfl
theorem dir320_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 320 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
