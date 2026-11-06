import NetHack.Sokoban32Refined.Directions24
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir279_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 .north p = true := by
  rfl
theorem dir279_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 .south p = true := by
  rfl
theorem dir279_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 .east p = true := by
  change ((!walkGuard soko3_2.board support p 279 280 .east || decide (bonus 279 p ≤ bonus 280 p)) && ((PreciseRolling.stayTargets soko3_2.board 280 .east).all (fun landing => !pushGuard support p 279 280 281 landing || decide (bonus 279 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 280 + bonus 280 (change p 280 (some landing)))) && (pushTargets soko3_2.board 280 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 279 280 281 landing || decide (bonus 279 p ≤ 1 - Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.hole landing + bonus 280 (change p 280 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1235 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1236 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1237 p, (by intro cell member; cases member)⟩)
theorem dir279_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 .west p = true := by
  change ((!walkGuard soko3_2.board support p 279 278 .west || decide (bonus 279 p ≤ bonus 278 p)) && ((PreciseRolling.stayTargets soko3_2.board 278 .west).all (fun landing => !pushGuard support p 279 278 277 landing || decide (bonus 279 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 278 + bonus 278 (change p 278 (some landing)))) && (pushTargets soko3_2.board 278 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 279 278 277 landing || decide (bonus 279 p ≤ 1 - Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.hole landing + bonus 278 (change p 278 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1238 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1239 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1240 p, (by intro cell member; cases member)⟩)
theorem dir279_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 .northEast p = true := by
  rfl
theorem dir279_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 .northWest p = true := by
  rfl
theorem dir279_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 .southEast p = true := by
  rfl
theorem dir279_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 279 .southWest p = true := by
  rfl
theorem dir280_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 .north p = true := by
  rfl
theorem dir280_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 .south p = true := by
  rfl
theorem dir280_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 .east p = true := by
  change ((!walkGuard soko3_2.board support p 280 281 .east || decide (bonus 280 p ≤ bonus 281 p)) && ((PreciseRolling.stayTargets soko3_2.board 281 .east).all (fun landing => !pushGuard support p 280 281 282 landing || decide (bonus 280 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 281 + bonus 281 (change p 281 (some landing)))) && (pushTargets soko3_2.board 281 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 280 281 282 landing || decide (bonus 280 p ≤ 1 - Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.hole landing + bonus 281 (change p 281 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1241 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1242 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1243 p, (by intro cell member; cases member)⟩)
theorem dir280_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 .west p = true := by
  change ((!walkGuard soko3_2.board support p 280 279 .west || decide (bonus 280 p ≤ bonus 279 p)) && ((PreciseRolling.stayTargets soko3_2.board 279 .west).all (fun landing => !pushGuard support p 280 279 278 landing || decide (bonus 280 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 279 + bonus 279 (change p 279 (some landing)))) && (pushTargets soko3_2.board 279 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 280 279 278 landing || decide (bonus 280 p ≤ 1 - Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.hole landing + bonus 279 (change p 279 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1244 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1245 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1246 p, (by intro cell member; cases member)⟩)
theorem dir280_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 .northEast p = true := by
  rfl
theorem dir280_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 .northWest p = true := by
  rfl
theorem dir280_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 .southEast p = true := by
  rfl
theorem dir280_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 280 .southWest p = true := by
  rfl
theorem dir281_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 .north p = true := by
  rfl
theorem dir281_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 .south p = true := by
  rfl
theorem dir281_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 .east p = true := by
  change ((!walkGuard soko3_2.board support p 281 282 .east || decide (bonus 281 p ≤ bonus 282 p)) && ((PreciseRolling.stayTargets soko3_2.board 282 .east).all (fun landing => !pushGuard support p 281 282 283 landing || decide (bonus 281 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 282 + bonus 282 (change p 282 (some landing)))) && (pushTargets soko3_2.board 282 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 281 282 283 landing || decide (bonus 281 p ≤ 1 - Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.hole landing + bonus 282 (change p 282 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1247 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1248 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1249 p, (by intro cell member; cases member)⟩)
theorem dir281_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 .west p = true := by
  change ((!walkGuard soko3_2.board support p 281 280 .west || decide (bonus 281 p ≤ bonus 280 p)) && ((PreciseRolling.stayTargets soko3_2.board 280 .west).all (fun landing => !pushGuard support p 281 280 279 landing || decide (bonus 281 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 280 + bonus 280 (change p 280 (some landing)))) && (pushTargets soko3_2.board 280 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 281 280 279 landing || decide (bonus 281 p ≤ 1 - Generated.soko3_2Potential.boulder 280 - Generated.soko3_2Potential.hole landing + bonus 280 (change p 280 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1250 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1251 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1252 p, (by intro cell member; cases member)⟩)
theorem dir281_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 .northEast p = true := by
  rfl
theorem dir281_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 .northWest p = true := by
  rfl
theorem dir281_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 .southEast p = true := by
  rfl
theorem dir281_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 281 .southWest p = true := by
  rfl
theorem dir282_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 .north p = true := by
  rfl
theorem dir282_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 .south p = true := by
  rfl
theorem dir282_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 .east p = true := by
  change ((!walkGuard soko3_2.board support p 282 283 .east || decide (bonus 282 p ≤ bonus 283 p)) && ((PreciseRolling.stayTargets soko3_2.board 283 .east).all (fun landing => !pushGuard support p 282 283 284 landing || decide (bonus 282 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 283 + bonus 283 (change p 283 (some landing)))) && (pushTargets soko3_2.board 283 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 282 283 284 landing || decide (bonus 282 p ≤ 1 - Generated.soko3_2Potential.boulder 283 - Generated.soko3_2Potential.hole landing + bonus 283 (change p 283 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1253 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1254 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir282_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 .west p = true := by
  change ((!walkGuard soko3_2.board support p 282 281 .west || decide (bonus 282 p ≤ bonus 281 p)) && ((PreciseRolling.stayTargets soko3_2.board 281 .west).all (fun landing => !pushGuard support p 282 281 280 landing || decide (bonus 282 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 281 + bonus 281 (change p 281 (some landing)))) && (pushTargets soko3_2.board 281 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 282 281 280 landing || decide (bonus 282 p ≤ 1 - Generated.soko3_2Potential.boulder 281 - Generated.soko3_2Potential.hole landing + bonus 281 (change p 281 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1255 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1256 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1257 p, (by intro cell member; cases member)⟩)
theorem dir282_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 .northEast p = true := by
  rfl
theorem dir282_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 .northWest p = true := by
  rfl
theorem dir282_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 .southEast p = true := by
  rfl
theorem dir282_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 282 .southWest p = true := by
  rfl
theorem dir283_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 .north p = true := by
  rfl
theorem dir283_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 .south p = true := by
  rfl
theorem dir283_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 .east p = true := by
  change ((!walkGuard soko3_2.board support p 283 284 .east || decide (bonus 283 p ≤ bonus 284 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1258 p, rfl⟩
theorem dir283_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 .west p = true := by
  change ((!walkGuard soko3_2.board support p 283 282 .west || decide (bonus 283 p ≤ bonus 282 p)) && ((PreciseRolling.stayTargets soko3_2.board 282 .west).all (fun landing => !pushGuard support p 283 282 281 landing || decide (bonus 283 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 282 + bonus 282 (change p 282 (some landing)))) && (pushTargets soko3_2.board 282 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 283 282 281 landing || decide (bonus 283 p ≤ 1 - Generated.soko3_2Potential.boulder 282 - Generated.soko3_2Potential.hole landing + bonus 282 (change p 282 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1259 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1260 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1261 p, (by intro cell member; cases member)⟩)
theorem dir283_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 .northEast p = true := by
  rfl
theorem dir283_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 .northWest p = true := by
  rfl
theorem dir283_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 .southEast p = true := by
  rfl
theorem dir283_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 283 .southWest p = true := by
  rfl
theorem dir284_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 .north p = true := by
  rfl
theorem dir284_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 .south p = true := by
  rfl
theorem dir284_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 .east p = true := by
  rfl
theorem dir284_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 .west p = true := by
  change ((!walkGuard soko3_2.board support p 284 283 .west || decide (bonus 284 p ≤ bonus 283 p)) && ((PreciseRolling.stayTargets soko3_2.board 283 .west).all (fun landing => !pushGuard support p 284 283 282 landing || decide (bonus 284 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 283 + bonus 283 (change p 283 (some landing)))) && (pushTargets soko3_2.board 283 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 284 283 282 landing || decide (bonus 284 p ≤ 1 - Generated.soko3_2Potential.boulder 283 - Generated.soko3_2Potential.hole landing + bonus 283 (change p 283 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1262 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1263 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1264 p, (by intro cell member; cases member)⟩)
theorem dir284_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 .northEast p = true := by
  rfl
theorem dir284_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 .northWest p = true := by
  rfl
theorem dir284_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 .southEast p = true := by
  rfl
theorem dir284_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 284 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
