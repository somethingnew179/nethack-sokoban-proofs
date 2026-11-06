import NetHack.Sokoban22Refined85.Directions05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir100_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 .north p = true := by
  change ((!walkGuard soko2_2.board support p 100 78 .north || decide (bonus 100 p ≤ bonus 78 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check254 p, rfl⟩
theorem dir100_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 .south p = true := by
  change ((!walkGuard soko2_2.board support p 100 122 .south || decide (bonus 100 p ≤ bonus 122 p)) && ((PreciseRolling.stayTargets soko2_2.board 122 .south).all (fun landing => !pushGuard support p 100 122 144 landing || decide (bonus 100 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 122 + bonus 122 (change p 122 (some landing)))) && (pushTargets soko2_2.board 122 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 100 122 144 landing || decide (bonus 100 p ≤ 1 - Generated.soko2_2Potential.boulder 122 - Generated.soko2_2Potential.hole landing + bonus 122 (change p 122 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check255 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check256 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir100_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 .east p = true := by
  change ((!walkGuard soko2_2.board support p 100 101 .east || decide (bonus 100 p ≤ bonus 101 p)) && ((PreciseRolling.stayTargets soko2_2.board 101 .east).all (fun landing => !pushGuard support p 100 101 102 landing || decide (bonus 100 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some landing)))) && (pushTargets soko2_2.board 101 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 100 101 102 landing || decide (bonus 100 p ≤ 1 - Generated.soko2_2Potential.boulder 101 - Generated.soko2_2Potential.hole landing + bonus 101 (change p 101 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check257 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check258 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir100_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 .west p = true := by
  rfl
theorem dir100_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 100 79 .northEast || decide (bonus 100 p ≤ bonus 79 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check259 p, rfl⟩
theorem dir100_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 .northWest p = true := by
  rfl
theorem dir100_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 100 123 .southEast || decide (bonus 100 p ≤ bonus 123 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check260 p, rfl⟩
theorem dir100_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 100 .southWest p = true := by
  rfl
theorem dir101_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 .north p = true := by
  change ((!walkGuard soko2_2.board support p 101 79 .north || decide (bonus 101 p ≤ bonus 79 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check261 p, rfl⟩
theorem dir101_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 .south p = true := by
  change ((!walkGuard soko2_2.board support p 101 123 .south || decide (bonus 101 p ≤ bonus 123 p)) && ((PreciseRolling.stayTargets soko2_2.board 123 .south).all (fun landing => !pushGuard support p 101 123 145 landing || decide (bonus 101 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some landing)))) && (pushTargets soko2_2.board 123 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 101 123 145 landing || decide (bonus 101 p ≤ 1 - Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.hole landing + bonus 123 (change p 123 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check262 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check263 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir101_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 .east p = true := by
  change ((!walkGuard soko2_2.board support p 101 102 .east || decide (bonus 101 p ≤ bonus 102 p)) && ((PreciseRolling.stayTargets soko2_2.board 102 .east).all (fun landing => !pushGuard support p 101 102 103 landing || decide (bonus 101 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some landing)))) && (pushTargets soko2_2.board 102 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 101 102 103 landing || decide (bonus 101 p ≤ 1 - Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.hole landing + bonus 102 (change p 102 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check264 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check265 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir101_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 .west p = true := by
  change ((!walkGuard soko2_2.board support p 101 100 .west || decide (bonus 101 p ≤ bonus 100 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check266 p, rfl⟩
theorem dir101_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 101 80 .northEast || decide (bonus 101 p ≤ bonus 80 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check267 p, rfl⟩
theorem dir101_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 101 78 .northWest || decide (bonus 101 p ≤ bonus 78 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check268 p, rfl⟩
theorem dir101_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 101 124 .southEast || decide (bonus 101 p ≤ bonus 124 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check269 p, rfl⟩
theorem dir101_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 101 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 101 122 .southWest || decide (bonus 101 p ≤ bonus 122 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check270 p, rfl⟩
theorem dir102_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 .north p = true := by
  change ((!walkGuard soko2_2.board support p 102 80 .north || decide (bonus 102 p ≤ bonus 80 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check271 p, rfl⟩
theorem dir102_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 .south p = true := by
  change ((!walkGuard soko2_2.board support p 102 124 .south || decide (bonus 102 p ≤ bonus 124 p)) && ((PreciseRolling.stayTargets soko2_2.board 124 .south).all (fun landing => !pushGuard support p 102 124 146 landing || decide (bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some landing)))) && (pushTargets soko2_2.board 124 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 102 124 146 landing || decide (bonus 102 p ≤ 1 - Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.hole landing + bonus 124 (change p 124 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check272 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check273 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir102_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 .east p = true := by
  change ((!walkGuard soko2_2.board support p 102 103 .east || decide (bonus 102 p ≤ bonus 103 p)) && ((PreciseRolling.stayTargets soko2_2.board 103 .east).all (fun landing => !pushGuard support p 102 103 104 landing || decide (bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some landing)))) && (pushTargets soko2_2.board 103 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 102 103 104 landing || decide (bonus 102 p ≤ 1 - Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.hole landing + bonus 103 (change p 103 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check274 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check275 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir102_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 .west p = true := by
  change ((!walkGuard soko2_2.board support p 102 101 .west || decide (bonus 102 p ≤ bonus 101 p)) && ((PreciseRolling.stayTargets soko2_2.board 101 .west).all (fun landing => !pushGuard support p 102 101 100 landing || decide (bonus 102 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some landing)))) && (pushTargets soko2_2.board 101 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 102 101 100 landing || decide (bonus 102 p ≤ 1 - Generated.soko2_2Potential.boulder 101 - Generated.soko2_2Potential.hole landing + bonus 101 (change p 101 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check276 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check277 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir102_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 102 81 .northEast || decide (bonus 102 p ≤ bonus 81 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check278 p, rfl⟩
theorem dir102_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 102 79 .northWest || decide (bonus 102 p ≤ bonus 79 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check279 p, rfl⟩
theorem dir102_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 102 125 .southEast || decide (bonus 102 p ≤ bonus 125 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check280 p, rfl⟩
theorem dir102_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 102 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 102 123 .southWest || decide (bonus 102 p ≤ bonus 123 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check281 p, rfl⟩
theorem dir103_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 .north p = true := by
  change ((!walkGuard soko2_2.board support p 103 81 .north || decide (bonus 103 p ≤ bonus 81 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check282 p, rfl⟩
theorem dir103_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 .south p = true := by
  change ((!walkGuard soko2_2.board support p 103 125 .south || decide (bonus 103 p ≤ bonus 125 p)) && ((PreciseRolling.stayTargets soko2_2.board 125 .south).all (fun landing => !pushGuard support p 103 125 147 landing || decide (bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some landing)))) && (pushTargets soko2_2.board 125 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 103 125 147 landing || decide (bonus 103 p ≤ 1 - Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.hole landing + bonus 125 (change p 125 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check283 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check284 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir103_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 .east p = true := by
  change ((!walkGuard soko2_2.board support p 103 104 .east || decide (bonus 103 p ≤ bonus 104 p)) && ((PreciseRolling.stayTargets soko2_2.board 104 .east).all (fun landing => !pushGuard support p 103 104 105 landing || decide (bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some landing)))) && (pushTargets soko2_2.board 104 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 103 104 105 landing || decide (bonus 103 p ≤ 1 - Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.hole landing + bonus 104 (change p 104 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check285 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check286 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir103_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 .west p = true := by
  change ((!walkGuard soko2_2.board support p 103 102 .west || decide (bonus 103 p ≤ bonus 102 p)) && ((PreciseRolling.stayTargets soko2_2.board 102 .west).all (fun landing => !pushGuard support p 103 102 101 landing || decide (bonus 103 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some landing)))) && (pushTargets soko2_2.board 102 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 103 102 101 landing || decide (bonus 103 p ≤ 1 - Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.hole landing + bonus 102 (change p 102 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check287 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check288 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir103_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 103 82 .northEast || decide (bonus 103 p ≤ bonus 82 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check289 p, rfl⟩
theorem dir103_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 103 80 .northWest || decide (bonus 103 p ≤ bonus 80 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check290 p, rfl⟩
theorem dir103_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 103 126 .southEast || decide (bonus 103 p ≤ bonus 126 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check291 p, rfl⟩
theorem dir103_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 103 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 103 124 .southWest || decide (bonus 103 p ≤ bonus 124 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check292 p, rfl⟩
theorem dir104_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 .north p = true := by
  change ((!walkGuard soko2_2.board support p 104 82 .north || decide (bonus 104 p ≤ bonus 82 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check293 p, rfl⟩
theorem dir104_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 .south p = true := by
  change ((!walkGuard soko2_2.board support p 104 126 .south || decide (bonus 104 p ≤ bonus 126 p)) && ((PreciseRolling.stayTargets soko2_2.board 126 .south).all (fun landing => !pushGuard support p 104 126 148 landing || decide (bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some landing)))) && (pushTargets soko2_2.board 126 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 104 126 148 landing || decide (bonus 104 p ≤ 1 - Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.hole landing + bonus 126 (change p 126 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check294 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check295 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir104_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 .east p = true := by
  change ((!walkGuard soko2_2.board support p 104 105 .east || decide (bonus 104 p ≤ bonus 105 p)) && ((PreciseRolling.stayTargets soko2_2.board 105 .east).all (fun landing => !pushGuard support p 104 105 106 landing || decide (bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some landing)))) && (pushTargets soko2_2.board 105 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 104 105 106 landing || decide (bonus 104 p ≤ 1 - Generated.soko2_2Potential.boulder 105 - Generated.soko2_2Potential.hole landing + bonus 105 (change p 105 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check296 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check297 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir104_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 .west p = true := by
  change ((!walkGuard soko2_2.board support p 104 103 .west || decide (bonus 104 p ≤ bonus 103 p)) && ((PreciseRolling.stayTargets soko2_2.board 103 .west).all (fun landing => !pushGuard support p 104 103 102 landing || decide (bonus 104 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some landing)))) && (pushTargets soko2_2.board 103 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 104 103 102 landing || decide (bonus 104 p ≤ 1 - Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.hole landing + bonus 103 (change p 103 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check298 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check299 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir104_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 104 83 .northEast || decide (bonus 104 p ≤ bonus 83 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check300 p, rfl⟩
theorem dir104_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 104 81 .northWest || decide (bonus 104 p ≤ bonus 81 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check301 p, rfl⟩
theorem dir104_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 104 127 .southEast || decide (bonus 104 p ≤ bonus 127 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check302 p, rfl⟩
theorem dir104_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 104 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 104 125 .southWest || decide (bonus 104 p ≤ bonus 125 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check303 p, rfl⟩
theorem dir105_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 .north p = true := by
  change ((!walkGuard soko2_2.board support p 105 83 .north || decide (bonus 105 p ≤ bonus 83 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check304 p, rfl⟩
theorem dir105_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 .south p = true := by
  change ((!walkGuard soko2_2.board support p 105 127 .south || decide (bonus 105 p ≤ bonus 127 p)) && ((PreciseRolling.stayTargets soko2_2.board 127 .south).all (fun landing => !pushGuard support p 105 127 149 landing || decide (bonus 105 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some landing)))) && (pushTargets soko2_2.board 127 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 105 127 149 landing || decide (bonus 105 p ≤ 1 - Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.hole landing + bonus 127 (change p 127 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check305 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check306 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir105_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 .east p = true := by
  change ((!walkGuard soko2_2.board support p 105 106 .east || decide (bonus 105 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check307 p, rfl⟩
theorem dir105_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 .west p = true := by
  change ((!walkGuard soko2_2.board support p 105 104 .west || decide (bonus 105 p ≤ bonus 104 p)) && ((PreciseRolling.stayTargets soko2_2.board 104 .west).all (fun landing => !pushGuard support p 105 104 103 landing || decide (bonus 105 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some landing)))) && (pushTargets soko2_2.board 104 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 105 104 103 landing || decide (bonus 105 p ≤ 1 - Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.hole landing + bonus 104 (change p 104 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check308 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check309 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir105_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 105 84 .northEast || decide (bonus 105 p ≤ bonus 84 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check310 p, rfl⟩
theorem dir105_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 105 82 .northWest || decide (bonus 105 p ≤ bonus 82 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check311 p, rfl⟩
theorem dir105_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 105 128 .southEast || decide (bonus 105 p ≤ bonus 128 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check312 p, rfl⟩
theorem dir105_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 105 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 105 126 .southWest || decide (bonus 105 p ≤ bonus 126 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check313 p, rfl⟩
end NetHack.Sokoban22Refined85
