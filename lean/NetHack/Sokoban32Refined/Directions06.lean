import NetHack.Sokoban32Refined.Directions05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir96_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 .north p = true := by
  change ((!walkGuard soko3_2.board support p 96 70 .north || decide (bonus 96 p ≤ bonus 70 p)) && ((PreciseRolling.stayTargets soko3_2.board 70 .north).all (fun landing => !pushGuard support p 96 70 44 landing || decide (bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some landing)))) && (pushTargets soko3_2.board 70 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 96 70 44 landing || decide (bonus 96 p ≤ 1 - Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.hole landing + bonus 70 (change p 70 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check259 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check260 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir96_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 .south p = true := by
  change ((!walkGuard soko3_2.board support p 96 122 .south || decide (bonus 96 p ≤ bonus 122 p)) && ((PreciseRolling.stayTargets soko3_2.board 122 .south).all (fun landing => !pushGuard support p 96 122 148 landing || decide (bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some landing)))) && (pushTargets soko3_2.board 122 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 96 122 148 landing || decide (bonus 96 p ≤ 1 - Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.hole landing + bonus 122 (change p 122 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check261 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check262 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir96_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 .east p = true := by
  change ((!walkGuard soko3_2.board support p 96 97 .east || decide (bonus 96 p ≤ bonus 97 p)) && ((PreciseRolling.stayTargets soko3_2.board 97 .east).all (fun landing => !pushGuard support p 96 97 98 landing || decide (bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some landing)))) && (pushTargets soko3_2.board 97 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 96 97 98 landing || decide (bonus 96 p ≤ 1 - Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.hole landing + bonus 97 (change p 97 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check263 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check264 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir96_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 .west p = true := by
  change ((!walkGuard soko3_2.board support p 96 95 .west || decide (bonus 96 p ≤ bonus 95 p)) && ((PreciseRolling.stayTargets soko3_2.board 95 .west).all (fun landing => !pushGuard support p 96 95 94 landing || decide (bonus 96 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some landing)))) && (pushTargets soko3_2.board 95 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 96 95 94 landing || decide (bonus 96 p ≤ 1 - Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.hole landing + bonus 95 (change p 95 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check265 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check266 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir96_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 96 71 .northEast || decide (bonus 96 p ≤ bonus 71 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check267 p, rfl⟩
theorem dir96_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 96 69 .northWest || decide (bonus 96 p ≤ bonus 69 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check268 p, rfl⟩
theorem dir96_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 96 123 .southEast || decide (bonus 96 p ≤ bonus 123 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check269 p, rfl⟩
theorem dir96_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 96 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 96 121 .southWest || decide (bonus 96 p ≤ bonus 121 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check270 p, rfl⟩
theorem dir97_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 .north p = true := by
  change ((!walkGuard soko3_2.board support p 97 71 .north || decide (bonus 97 p ≤ bonus 71 p)) && ((PreciseRolling.stayTargets soko3_2.board 71 .north).all (fun landing => !pushGuard support p 97 71 45 landing || decide (bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some landing)))) && (pushTargets soko3_2.board 71 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 97 71 45 landing || decide (bonus 97 p ≤ 1 - Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.hole landing + bonus 71 (change p 71 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check271 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check272 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir97_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 .south p = true := by
  change ((!walkGuard soko3_2.board support p 97 123 .south || decide (bonus 97 p ≤ bonus 123 p)) && ((PreciseRolling.stayTargets soko3_2.board 123 .south).all (fun landing => !pushGuard support p 97 123 149 landing || decide (bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some landing)))) && (pushTargets soko3_2.board 123 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 97 123 149 landing || decide (bonus 97 p ≤ 1 - Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.hole landing + bonus 123 (change p 123 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check273 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check274 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir97_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 .east p = true := by
  change ((!walkGuard soko3_2.board support p 97 98 .east || decide (bonus 97 p ≤ bonus 98 p)) && ((PreciseRolling.stayTargets soko3_2.board 98 .east).all (fun landing => !pushGuard support p 97 98 99 landing || decide (bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some landing)))) && (pushTargets soko3_2.board 98 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 97 98 99 landing || decide (bonus 97 p ≤ 1 - Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.hole landing + bonus 98 (change p 98 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check275 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check276 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir97_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 .west p = true := by
  change ((!walkGuard soko3_2.board support p 97 96 .west || decide (bonus 97 p ≤ bonus 96 p)) && ((PreciseRolling.stayTargets soko3_2.board 96 .west).all (fun landing => !pushGuard support p 97 96 95 landing || decide (bonus 97 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some landing)))) && (pushTargets soko3_2.board 96 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 97 96 95 landing || decide (bonus 97 p ≤ 1 - Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.hole landing + bonus 96 (change p 96 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check277 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check278 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir97_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 97 72 .northEast || decide (bonus 97 p ≤ bonus 72 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check279 p, rfl⟩
theorem dir97_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 97 70 .northWest || decide (bonus 97 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check280 p, rfl⟩
theorem dir97_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 97 124 .southEast || decide (bonus 97 p ≤ bonus 124 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check281 p, rfl⟩
theorem dir97_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 97 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 97 122 .southWest || decide (bonus 97 p ≤ bonus 122 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check282 p, rfl⟩
theorem dir98_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 .north p = true := by
  change ((!walkGuard soko3_2.board support p 98 72 .north || decide (bonus 98 p ≤ bonus 72 p)) && ((PreciseRolling.stayTargets soko3_2.board 72 .north).all (fun landing => !pushGuard support p 98 72 46 landing || decide (bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some landing)))) && (pushTargets soko3_2.board 72 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 98 72 46 landing || decide (bonus 98 p ≤ 1 - Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.hole landing + bonus 72 (change p 72 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check283 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check284 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir98_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 .south p = true := by
  change ((!walkGuard soko3_2.board support p 98 124 .south || decide (bonus 98 p ≤ bonus 124 p)) && ((PreciseRolling.stayTargets soko3_2.board 124 .south).all (fun landing => !pushGuard support p 98 124 150 landing || decide (bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some landing)))) && (pushTargets soko3_2.board 124 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 98 124 150 landing || decide (bonus 98 p ≤ 1 - Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.hole landing + bonus 124 (change p 124 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check285 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check286 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir98_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 .east p = true := by
  change ((!walkGuard soko3_2.board support p 98 99 .east || decide (bonus 98 p ≤ bonus 99 p)) && ((PreciseRolling.stayTargets soko3_2.board 99 .east).all (fun landing => !pushGuard support p 98 99 100 landing || decide (bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some landing)))) && (pushTargets soko3_2.board 99 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 98 99 100 landing || decide (bonus 98 p ≤ 1 - Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.hole landing + bonus 99 (change p 99 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check287 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check288 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir98_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 .west p = true := by
  change ((!walkGuard soko3_2.board support p 98 97 .west || decide (bonus 98 p ≤ bonus 97 p)) && ((PreciseRolling.stayTargets soko3_2.board 97 .west).all (fun landing => !pushGuard support p 98 97 96 landing || decide (bonus 98 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some landing)))) && (pushTargets soko3_2.board 97 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 98 97 96 landing || decide (bonus 98 p ≤ 1 - Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.hole landing + bonus 97 (change p 97 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check289 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check290 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir98_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 98 73 .northEast || decide (bonus 98 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check291 p, rfl⟩
theorem dir98_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 98 71 .northWest || decide (bonus 98 p ≤ bonus 71 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check292 p, rfl⟩
theorem dir98_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 98 125 .southEast || decide (bonus 98 p ≤ bonus 125 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check293 p, rfl⟩
theorem dir98_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 98 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 98 123 .southWest || decide (bonus 98 p ≤ bonus 123 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check294 p, rfl⟩
theorem dir99_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 .north p = true := by
  change ((!walkGuard soko3_2.board support p 99 73 .north || decide (bonus 99 p ≤ bonus 73 p)) && ((PreciseRolling.stayTargets soko3_2.board 73 .north).all (fun landing => !pushGuard support p 99 73 47 landing || decide (bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some landing)))) && (pushTargets soko3_2.board 73 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 99 73 47 landing || decide (bonus 99 p ≤ 1 - Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.hole landing + bonus 73 (change p 73 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check295 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check296 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir99_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 .south p = true := by
  change ((!walkGuard soko3_2.board support p 99 125 .south || decide (bonus 99 p ≤ bonus 125 p)) && ((PreciseRolling.stayTargets soko3_2.board 125 .south).all (fun landing => !pushGuard support p 99 125 151 landing || decide (bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some landing)))) && (pushTargets soko3_2.board 125 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 99 125 151 landing || decide (bonus 99 p ≤ 1 - Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.hole landing + bonus 125 (change p 125 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check297 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check298 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir99_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 .east p = true := by
  change ((!walkGuard soko3_2.board support p 99 100 .east || decide (bonus 99 p ≤ bonus 100 p)) && ((PreciseRolling.stayTargets soko3_2.board 100 .east).all (fun landing => !pushGuard support p 99 100 101 landing || decide (bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some landing)))) && (pushTargets soko3_2.board 100 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 99 100 101 landing || decide (bonus 99 p ≤ 1 - Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.hole landing + bonus 100 (change p 100 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check299 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check300 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir99_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 .west p = true := by
  change ((!walkGuard soko3_2.board support p 99 98 .west || decide (bonus 99 p ≤ bonus 98 p)) && ((PreciseRolling.stayTargets soko3_2.board 98 .west).all (fun landing => !pushGuard support p 99 98 97 landing || decide (bonus 99 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some landing)))) && (pushTargets soko3_2.board 98 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 99 98 97 landing || decide (bonus 99 p ≤ 1 - Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.hole landing + bonus 98 (change p 98 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check301 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check302 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir99_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 99 74 .northEast || decide (bonus 99 p ≤ bonus 74 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check303 p, rfl⟩
theorem dir99_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 99 72 .northWest || decide (bonus 99 p ≤ bonus 72 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check304 p, rfl⟩
theorem dir99_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 99 126 .southEast || decide (bonus 99 p ≤ bonus 126 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check305 p, rfl⟩
theorem dir99_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 99 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 99 124 .southWest || decide (bonus 99 p ≤ bonus 124 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check306 p, rfl⟩
theorem dir100_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 .north p = true := by
  change ((!walkGuard soko3_2.board support p 100 74 .north || decide (bonus 100 p ≤ bonus 74 p)) && ((PreciseRolling.stayTargets soko3_2.board 74 .north).all (fun landing => !pushGuard support p 100 74 48 landing || decide (bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some landing)))) && (pushTargets soko3_2.board 74 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 100 74 48 landing || decide (bonus 100 p ≤ 1 - Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.hole landing + bonus 74 (change p 74 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check307 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check308 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir100_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 .south p = true := by
  change ((!walkGuard soko3_2.board support p 100 126 .south || decide (bonus 100 p ≤ bonus 126 p)) && ((PreciseRolling.stayTargets soko3_2.board 126 .south).all (fun landing => !pushGuard support p 100 126 152 landing || decide (bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some landing)))) && (pushTargets soko3_2.board 126 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 100 126 152 landing || decide (bonus 100 p ≤ 1 - Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.hole landing + bonus 126 (change p 126 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check309 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check310 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir100_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 .east p = true := by
  change ((!walkGuard soko3_2.board support p 100 101 .east || decide (bonus 100 p ≤ bonus 101 p)) && ((PreciseRolling.stayTargets soko3_2.board 101 .east).all (fun landing => !pushGuard support p 100 101 102 landing || decide (bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some landing)))) && (pushTargets soko3_2.board 101 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 100 101 102 landing || decide (bonus 100 p ≤ 1 - Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.hole landing + bonus 101 (change p 101 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check311 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check312 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir100_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 .west p = true := by
  change ((!walkGuard soko3_2.board support p 100 99 .west || decide (bonus 100 p ≤ bonus 99 p)) && ((PreciseRolling.stayTargets soko3_2.board 99 .west).all (fun landing => !pushGuard support p 100 99 98 landing || decide (bonus 100 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some landing)))) && (pushTargets soko3_2.board 99 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 100 99 98 landing || decide (bonus 100 p ≤ 1 - Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.hole landing + bonus 99 (change p 99 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check313 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check314 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir100_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 100 75 .northEast || decide (bonus 100 p ≤ bonus 75 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check315 p, rfl⟩
theorem dir100_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 100 73 .northWest || decide (bonus 100 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check316 p, rfl⟩
theorem dir100_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 100 127 .southEast || decide (bonus 100 p ≤ bonus 127 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check317 p, rfl⟩
theorem dir100_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 100 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 100 125 .southWest || decide (bonus 100 p ≤ bonus 125 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check318 p, rfl⟩
theorem dir101_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 .north p = true := by
  change ((!walkGuard soko3_2.board support p 101 75 .north || decide (bonus 101 p ≤ bonus 75 p)) && ((PreciseRolling.stayTargets soko3_2.board 75 .north).all (fun landing => !pushGuard support p 101 75 49 landing || decide (bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some landing)))) && (pushTargets soko3_2.board 75 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 101 75 49 landing || decide (bonus 101 p ≤ 1 - Generated.soko3_2Potential.boulder 75 - Generated.soko3_2Potential.hole landing + bonus 75 (change p 75 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check319 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check320 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir101_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 .south p = true := by
  change ((!walkGuard soko3_2.board support p 101 127 .south || decide (bonus 101 p ≤ bonus 127 p)) && ((PreciseRolling.stayTargets soko3_2.board 127 .south).all (fun landing => !pushGuard support p 101 127 153 landing || decide (bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some landing)))) && (pushTargets soko3_2.board 127 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 101 127 153 landing || decide (bonus 101 p ≤ 1 - Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.hole landing + bonus 127 (change p 127 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check321 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check322 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir101_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 .east p = true := by
  change ((!walkGuard soko3_2.board support p 101 102 .east || decide (bonus 101 p ≤ bonus 102 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check323 p, rfl⟩
theorem dir101_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 .west p = true := by
  change ((!walkGuard soko3_2.board support p 101 100 .west || decide (bonus 101 p ≤ bonus 100 p)) && ((PreciseRolling.stayTargets soko3_2.board 100 .west).all (fun landing => !pushGuard support p 101 100 99 landing || decide (bonus 101 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some landing)))) && (pushTargets soko3_2.board 100 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 101 100 99 landing || decide (bonus 101 p ≤ 1 - Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.hole landing + bonus 100 (change p 100 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check324 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check325 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir101_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 101 76 .northEast || decide (bonus 101 p ≤ bonus 76 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check326 p, rfl⟩
theorem dir101_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 101 74 .northWest || decide (bonus 101 p ≤ bonus 74 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check327 p, rfl⟩
theorem dir101_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 101 128 .southEast || decide (bonus 101 p ≤ bonus 128 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check328 p, rfl⟩
theorem dir101_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 101 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 101 126 .southWest || decide (bonus 101 p ≤ bonus 126 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check329 p, rfl⟩
end NetHack.Sokoban32Refined
