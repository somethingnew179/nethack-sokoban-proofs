import NetHack.Sokoban32Refined.Directions23
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir273_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 .north p = true := by
  rfl
theorem dir273_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 .south p = true := by
  rfl
theorem dir273_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 .east p = true := by
  change ((!walkGuard soko3_2.board support p 273 274 .east || decide (bonus 273 p ≤ bonus 274 p)) && ((PreciseRolling.stayTargets soko3_2.board 274 .east).all (fun landing => !pushGuard support p 273 274 275 landing || decide (bonus 273 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 274 + bonus 274 (change p 274 (some landing)))) && (pushTargets soko3_2.board 274 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 273 274 275 landing || decide (bonus 273 p ≤ 1 - Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.hole landing + bonus 274 (change p 274 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1199 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1200 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1201 p, (by intro cell member; cases member)⟩)
theorem dir273_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 .west p = true := by
  change ((!walkGuard soko3_2.board support p 273 272 .west || decide (bonus 273 p ≤ bonus 272 p)) && ((PreciseRolling.stayTargets soko3_2.board 272 .west).all (fun landing => !pushGuard support p 273 272 271 landing || decide (bonus 273 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 272 + bonus 272 (change p 272 (some landing)))) && (pushTargets soko3_2.board 272 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 273 272 271 landing || decide (bonus 273 p ≤ 1 - Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.hole landing + bonus 272 (change p 272 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1202 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1203 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1204 p, (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)⟩)⟩)⟩)
theorem dir273_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 .northEast p = true := by
  rfl
theorem dir273_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 .northWest p = true := by
  rfl
theorem dir273_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 .southEast p = true := by
  rfl
theorem dir273_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 273 .southWest p = true := by
  rfl
theorem dir274_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 .north p = true := by
  rfl
theorem dir274_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 .south p = true := by
  rfl
theorem dir274_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 .east p = true := by
  change ((!walkGuard soko3_2.board support p 274 275 .east || decide (bonus 274 p ≤ bonus 275 p)) && ((PreciseRolling.stayTargets soko3_2.board 275 .east).all (fun landing => !pushGuard support p 274 275 276 landing || decide (bonus 274 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 275 + bonus 275 (change p 275 (some landing)))) && (pushTargets soko3_2.board 275 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 274 275 276 landing || decide (bonus 274 p ≤ 1 - Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.hole landing + bonus 275 (change p 275 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1205 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1206 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1207 p, (by intro cell member; cases member)⟩)
theorem dir274_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 .west p = true := by
  change ((!walkGuard soko3_2.board support p 274 273 .west || decide (bonus 274 p ≤ bonus 273 p)) && ((PreciseRolling.stayTargets soko3_2.board 273 .west).all (fun landing => !pushGuard support p 274 273 272 landing || decide (bonus 274 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 273 + bonus 273 (change p 273 (some landing)))) && (pushTargets soko3_2.board 273 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 274 273 272 landing || decide (bonus 274 p ≤ 1 - Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.hole landing + bonus 273 (change p 273 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1208 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1209 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1210 p, (by intro cell member; cases member)⟩)
theorem dir274_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 .northEast p = true := by
  rfl
theorem dir274_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 .northWest p = true := by
  rfl
theorem dir274_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 .southEast p = true := by
  rfl
theorem dir274_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 274 .southWest p = true := by
  rfl
theorem dir275_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 .north p = true := by
  rfl
theorem dir275_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 .south p = true := by
  rfl
theorem dir275_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 .east p = true := by
  change ((!walkGuard soko3_2.board support p 275 276 .east || decide (bonus 275 p ≤ bonus 276 p)) && ((PreciseRolling.stayTargets soko3_2.board 276 .east).all (fun landing => !pushGuard support p 275 276 277 landing || decide (bonus 275 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 276 + bonus 276 (change p 276 (some landing)))) && (pushTargets soko3_2.board 276 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 275 276 277 landing || decide (bonus 275 p ≤ 1 - Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.hole landing + bonus 276 (change p 276 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1211 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1212 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1213 p, (by intro cell member; cases member)⟩)
theorem dir275_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 .west p = true := by
  change ((!walkGuard soko3_2.board support p 275 274 .west || decide (bonus 275 p ≤ bonus 274 p)) && ((PreciseRolling.stayTargets soko3_2.board 274 .west).all (fun landing => !pushGuard support p 275 274 273 landing || decide (bonus 275 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 274 + bonus 274 (change p 274 (some landing)))) && (pushTargets soko3_2.board 274 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 275 274 273 landing || decide (bonus 275 p ≤ 1 - Generated.soko3_2Potential.boulder 274 - Generated.soko3_2Potential.hole landing + bonus 274 (change p 274 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1214 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1215 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1216 p, (by intro cell member; cases member)⟩)
theorem dir275_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 .northEast p = true := by
  rfl
theorem dir275_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 .northWest p = true := by
  rfl
theorem dir275_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 .southEast p = true := by
  rfl
theorem dir275_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 275 .southWest p = true := by
  rfl
theorem dir276_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 .north p = true := by
  rfl
theorem dir276_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 .south p = true := by
  rfl
theorem dir276_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 .east p = true := by
  change ((!walkGuard soko3_2.board support p 276 277 .east || decide (bonus 276 p ≤ bonus 277 p)) && ((PreciseRolling.stayTargets soko3_2.board 277 .east).all (fun landing => !pushGuard support p 276 277 278 landing || decide (bonus 276 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 277 + bonus 277 (change p 277 (some landing)))) && (pushTargets soko3_2.board 277 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 276 277 278 landing || decide (bonus 276 p ≤ 1 - Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.hole landing + bonus 277 (change p 277 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1217 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1218 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1219 p, (by intro cell member; cases member)⟩)
theorem dir276_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 .west p = true := by
  change ((!walkGuard soko3_2.board support p 276 275 .west || decide (bonus 276 p ≤ bonus 275 p)) && ((PreciseRolling.stayTargets soko3_2.board 275 .west).all (fun landing => !pushGuard support p 276 275 274 landing || decide (bonus 276 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 275 + bonus 275 (change p 275 (some landing)))) && (pushTargets soko3_2.board 275 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 276 275 274 landing || decide (bonus 276 p ≤ 1 - Generated.soko3_2Potential.boulder 275 - Generated.soko3_2Potential.hole landing + bonus 275 (change p 275 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1220 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1221 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1222 p, (by intro cell member; cases member)⟩)
theorem dir276_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 .northEast p = true := by
  rfl
theorem dir276_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 .northWest p = true := by
  rfl
theorem dir276_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 .southEast p = true := by
  rfl
theorem dir276_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 276 .southWest p = true := by
  rfl
theorem dir277_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 .north p = true := by
  rfl
theorem dir277_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 .south p = true := by
  rfl
theorem dir277_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 .east p = true := by
  change ((!walkGuard soko3_2.board support p 277 278 .east || decide (bonus 277 p ≤ bonus 278 p)) && ((PreciseRolling.stayTargets soko3_2.board 278 .east).all (fun landing => !pushGuard support p 277 278 279 landing || decide (bonus 277 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 278 + bonus 278 (change p 278 (some landing)))) && (pushTargets soko3_2.board 278 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 277 278 279 landing || decide (bonus 277 p ≤ 1 - Generated.soko3_2Potential.boulder 278 - Generated.soko3_2Potential.hole landing + bonus 278 (change p 278 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1223 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1224 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1225 p, (by intro cell member; cases member)⟩)
theorem dir277_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 .west p = true := by
  change ((!walkGuard soko3_2.board support p 277 276 .west || decide (bonus 277 p ≤ bonus 276 p)) && ((PreciseRolling.stayTargets soko3_2.board 276 .west).all (fun landing => !pushGuard support p 277 276 275 landing || decide (bonus 277 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 276 + bonus 276 (change p 276 (some landing)))) && (pushTargets soko3_2.board 276 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 277 276 275 landing || decide (bonus 277 p ≤ 1 - Generated.soko3_2Potential.boulder 276 - Generated.soko3_2Potential.hole landing + bonus 276 (change p 276 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1226 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1227 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1228 p, (by intro cell member; cases member)⟩)
theorem dir277_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 .northEast p = true := by
  rfl
theorem dir277_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 .northWest p = true := by
  rfl
theorem dir277_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 .southEast p = true := by
  rfl
theorem dir277_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 277 .southWest p = true := by
  rfl
theorem dir278_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 .north p = true := by
  rfl
theorem dir278_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 .south p = true := by
  rfl
theorem dir278_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 .east p = true := by
  change ((!walkGuard soko3_2.board support p 278 279 .east || decide (bonus 278 p ≤ bonus 279 p)) && ((PreciseRolling.stayTargets soko3_2.board 279 .east).all (fun landing => !pushGuard support p 278 279 280 landing || decide (bonus 278 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 279 + bonus 279 (change p 279 (some landing)))) && (pushTargets soko3_2.board 279 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 278 279 280 landing || decide (bonus 278 p ≤ 1 - Generated.soko3_2Potential.boulder 279 - Generated.soko3_2Potential.hole landing + bonus 279 (change p 279 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1229 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1230 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1231 p, (by intro cell member; cases member)⟩)
theorem dir278_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 .west p = true := by
  change ((!walkGuard soko3_2.board support p 278 277 .west || decide (bonus 278 p ≤ bonus 277 p)) && ((PreciseRolling.stayTargets soko3_2.board 277 .west).all (fun landing => !pushGuard support p 278 277 276 landing || decide (bonus 278 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 277 + bonus 277 (change p 277 (some landing)))) && (pushTargets soko3_2.board 277 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 278 277 276 landing || decide (bonus 278 p ≤ 1 - Generated.soko3_2Potential.boulder 277 - Generated.soko3_2Potential.hole landing + bonus 277 (change p 277 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1232 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1233 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1234 p, (by intro cell member; cases member)⟩)
theorem dir278_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 .northEast p = true := by
  rfl
theorem dir278_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 .northWest p = true := by
  rfl
theorem dir278_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 .southEast p = true := by
  rfl
theorem dir278_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 278 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
