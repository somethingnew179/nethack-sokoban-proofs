import NetHack.Sokoban32Refined.Directions27
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir321_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 .north p = true := by
  change ((!walkGuard soko3_2.board support p 321 295 .north || decide (bonus 321 p ≤ bonus 295 p)) && ((PreciseRolling.stayTargets soko3_2.board 295 .north).all (fun landing => !pushGuard support p 321 295 269 landing || decide (bonus 321 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 295 + bonus 295 (change p 295 (some landing)))) && (pushTargets soko3_2.board 295 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 321 295 269 landing || decide (bonus 321 p ≤ 1 - Generated.soko3_2Potential.boulder 295 - Generated.soko3_2Potential.hole landing + bonus 295 (change p 295 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1344 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1345 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir321_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 .south p = true := by
  rfl
theorem dir321_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 .east p = true := by
  rfl
theorem dir321_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 .west p = true := by
  change ((!walkGuard soko3_2.board support p 321 320 .west || decide (bonus 321 p ≤ bonus 320 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1346 p, rfl⟩
theorem dir321_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 .northEast p = true := by
  rfl
theorem dir321_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 321 294 .northWest || decide (bonus 321 p ≤ bonus 294 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1347 p, rfl⟩
theorem dir321_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 .southEast p = true := by
  rfl
theorem dir321_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 321 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
