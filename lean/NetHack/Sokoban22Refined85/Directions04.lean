import NetHack.Sokoban22Refined85.Directions03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir82_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 .north p = true := by
  rfl
theorem dir82_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 .south p = true := by
  change ((!walkGuard soko2_2.board support p 82 104 .south || decide (bonus 82 p ≤ bonus 104 p)) && ((PreciseRolling.stayTargets soko2_2.board 104 .south).all (fun landing => !pushGuard support p 82 104 126 landing || decide (bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 104 + bonus 104 (change p 104 (some landing)))) && (pushTargets soko2_2.board 104 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 82 104 126 landing || decide (bonus 82 p ≤ 1 - Generated.soko2_2Potential.boulder 104 - Generated.soko2_2Potential.hole landing + bonus 104 (change p 104 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check166 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check167 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir82_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 .east p = true := by
  change ((!walkGuard soko2_2.board support p 82 83 .east || decide (bonus 82 p ≤ bonus 83 p)) && ((PreciseRolling.stayTargets soko2_2.board 83 .east).all (fun landing => !pushGuard support p 82 83 84 landing || decide (bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 83 + bonus 83 (change p 83 (some landing)))) && (pushTargets soko2_2.board 83 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 82 83 84 landing || decide (bonus 82 p ≤ 1 - Generated.soko2_2Potential.boulder 83 - Generated.soko2_2Potential.hole landing + bonus 83 (change p 83 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check168 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check169 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir82_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 .west p = true := by
  change ((!walkGuard soko2_2.board support p 82 81 .west || decide (bonus 82 p ≤ bonus 81 p)) && ((PreciseRolling.stayTargets soko2_2.board 81 .west).all (fun landing => !pushGuard support p 82 81 80 landing || decide (bonus 82 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 81 + bonus 81 (change p 81 (some landing)))) && (pushTargets soko2_2.board 81 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 82 81 80 landing || decide (bonus 82 p ≤ 1 - Generated.soko2_2Potential.boulder 81 - Generated.soko2_2Potential.hole landing + bonus 81 (change p 81 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check170 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check171 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir82_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 .northEast p = true := by
  rfl
theorem dir82_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 .northWest p = true := by
  rfl
theorem dir82_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 82 105 .southEast || decide (bonus 82 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check172 p, rfl⟩
theorem dir82_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 82 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 82 103 .southWest || decide (bonus 82 p ≤ bonus 103 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check173 p, rfl⟩
theorem dir83_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 .north p = true := by
  rfl
theorem dir83_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 .south p = true := by
  change ((!walkGuard soko2_2.board support p 83 105 .south || decide (bonus 83 p ≤ bonus 105 p)) && ((PreciseRolling.stayTargets soko2_2.board 105 .south).all (fun landing => !pushGuard support p 83 105 127 landing || decide (bonus 83 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 105 + bonus 105 (change p 105 (some landing)))) && (pushTargets soko2_2.board 105 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 83 105 127 landing || decide (bonus 83 p ≤ 1 - Generated.soko2_2Potential.boulder 105 - Generated.soko2_2Potential.hole landing + bonus 105 (change p 105 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check174 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check175 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir83_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 .east p = true := by
  change ((!walkGuard soko2_2.board support p 83 84 .east || decide (bonus 83 p ≤ bonus 84 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check176 p, rfl⟩
theorem dir83_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 .west p = true := by
  change ((!walkGuard soko2_2.board support p 83 82 .west || decide (bonus 83 p ≤ bonus 82 p)) && ((PreciseRolling.stayTargets soko2_2.board 82 .west).all (fun landing => !pushGuard support p 83 82 81 landing || decide (bonus 83 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 82 + bonus 82 (change p 82 (some landing)))) && (pushTargets soko2_2.board 82 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 83 82 81 landing || decide (bonus 83 p ≤ 1 - Generated.soko2_2Potential.boulder 82 - Generated.soko2_2Potential.hole landing + bonus 82 (change p 82 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check177 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check178 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir83_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 .northEast p = true := by
  rfl
theorem dir83_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 .northWest p = true := by
  rfl
theorem dir83_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 83 106 .southEast || decide (bonus 83 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check179 p, rfl⟩
theorem dir83_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 83 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 83 104 .southWest || decide (bonus 83 p ≤ bonus 104 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check180 p, rfl⟩
theorem dir84_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 .north p = true := by
  rfl
theorem dir84_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 .south p = true := by
  change ((!walkGuard soko2_2.board support p 84 106 .south || decide (bonus 84 p ≤ bonus 106 p)) && ((PreciseRolling.stayTargets soko2_2.board 106 .south).all (fun landing => !pushGuard support p 84 106 128 landing || decide (bonus 84 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 106 + bonus 106 (change p 106 (some landing)))) && (pushTargets soko2_2.board 106 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 84 106 128 landing || decide (bonus 84 p ≤ 1 - Generated.soko2_2Potential.boulder 106 - Generated.soko2_2Potential.hole landing + bonus 106 (change p 106 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check181 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check182 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir84_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 .east p = true := by
  rfl
theorem dir84_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 .west p = true := by
  change ((!walkGuard soko2_2.board support p 84 83 .west || decide (bonus 84 p ≤ bonus 83 p)) && ((PreciseRolling.stayTargets soko2_2.board 83 .west).all (fun landing => !pushGuard support p 84 83 82 landing || decide (bonus 84 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 83 + bonus 83 (change p 83 (some landing)))) && (pushTargets soko2_2.board 83 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 84 83 82 landing || decide (bonus 84 p ≤ 1 - Generated.soko2_2Potential.boulder 83 - Generated.soko2_2Potential.hole landing + bonus 83 (change p 83 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check183 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check184 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir84_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 .northEast p = true := by
  rfl
theorem dir84_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 .northWest p = true := by
  rfl
theorem dir84_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 .southEast p = true := by
  rfl
theorem dir84_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 84 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 84 105 .southWest || decide (bonus 84 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check185 p, rfl⟩
theorem dir89_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 .north p = true := by
  change ((!walkGuard soko2_2.board support p 89 67 .north || decide (bonus 89 p ≤ bonus 67 p)) && ((PreciseRolling.stayTargets soko2_2.board 67 .north).all (fun landing => !pushGuard support p 89 67 45 landing || decide (bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 67 + bonus 67 (change p 67 (some landing)))) && (pushTargets soko2_2.board 67 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 89 67 45 landing || decide (bonus 89 p ≤ 1 - Generated.soko2_2Potential.boulder 67 - Generated.soko2_2Potential.hole landing + bonus 67 (change p 67 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check186 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check187 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir89_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 .south p = true := by
  change ((!walkGuard soko2_2.board support p 89 111 .south || decide (bonus 89 p ≤ bonus 111 p)) && ((PreciseRolling.stayTargets soko2_2.board 111 .south).all (fun landing => !pushGuard support p 89 111 133 landing || decide (bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 111 + bonus 111 (change p 111 (some landing)))) && (pushTargets soko2_2.board 111 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 89 111 133 landing || decide (bonus 89 p ≤ 1 - Generated.soko2_2Potential.boulder 111 - Generated.soko2_2Potential.hole landing + bonus 111 (change p 111 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check188 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check189 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir89_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 .east p = true := by
  change ((!walkGuard soko2_2.board support p 89 90 .east || decide (bonus 89 p ≤ bonus 90 p)) && ((PreciseRolling.stayTargets soko2_2.board 90 .east).all (fun landing => !pushGuard support p 89 90 91 landing || decide (bonus 89 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 90 + bonus 90 (change p 90 (some landing)))) && (pushTargets soko2_2.board 90 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 89 90 91 landing || decide (bonus 89 p ≤ 1 - Generated.soko2_2Potential.boulder 90 - Generated.soko2_2Potential.hole landing + bonus 90 (change p 90 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check190 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check191 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir89_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 .west p = true := by
  rfl
theorem dir89_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 .northEast p = true := by
  rfl
theorem dir89_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 .northWest p = true := by
  rfl
theorem dir89_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 .southEast p = true := by
  rfl
theorem dir89_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 89 .southWest p = true := by
  rfl
theorem dir90_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 .north p = true := by
  rfl
theorem dir90_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 .south p = true := by
  rfl
theorem dir90_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 .east p = true := by
  change ((!walkGuard soko2_2.board support p 90 91 .east || decide (bonus 90 p ≤ bonus 91 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check192 p, rfl⟩
theorem dir90_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 .west p = true := by
  change ((!walkGuard soko2_2.board support p 90 89 .west || decide (bonus 90 p ≤ bonus 89 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check193 p, rfl⟩
theorem dir90_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 90 69 .northEast || decide (bonus 90 p ≤ bonus 69 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check194 p, rfl⟩
theorem dir90_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 90 67 .northWest || decide (bonus 90 p ≤ bonus 67 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check195 p, rfl⟩
theorem dir90_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 90 113 .southEast || decide (bonus 90 p ≤ bonus 113 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check196 p, rfl⟩
theorem dir90_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 90 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 90 111 .southWest || decide (bonus 90 p ≤ bonus 111 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check197 p, rfl⟩
theorem dir91_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 .north p = true := by
  change ((!walkGuard soko2_2.board support p 91 69 .north || decide (bonus 91 p ≤ bonus 69 p)) && ((PreciseRolling.stayTargets soko2_2.board 69 .north).all (fun landing => !pushGuard support p 91 69 47 landing || decide (bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 69 + bonus 69 (change p 69 (some landing)))) && (pushTargets soko2_2.board 69 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 91 69 47 landing || decide (bonus 91 p ≤ 1 - Generated.soko2_2Potential.boulder 69 - Generated.soko2_2Potential.hole landing + bonus 69 (change p 69 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check198 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check199 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir91_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 .south p = true := by
  change ((!walkGuard soko2_2.board support p 91 113 .south || decide (bonus 91 p ≤ bonus 113 p)) && ((PreciseRolling.stayTargets soko2_2.board 113 .south).all (fun landing => !pushGuard support p 91 113 135 landing || decide (bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 113 + bonus 113 (change p 113 (some landing)))) && (pushTargets soko2_2.board 113 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 91 113 135 landing || decide (bonus 91 p ≤ 1 - Generated.soko2_2Potential.boulder 113 - Generated.soko2_2Potential.hole landing + bonus 113 (change p 113 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check200 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check201 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir91_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 .east p = true := by
  rfl
theorem dir91_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 .west p = true := by
  change ((!walkGuard soko2_2.board support p 91 90 .west || decide (bonus 91 p ≤ bonus 90 p)) && ((PreciseRolling.stayTargets soko2_2.board 90 .west).all (fun landing => !pushGuard support p 91 90 89 landing || decide (bonus 91 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 90 + bonus 90 (change p 90 (some landing)))) && (pushTargets soko2_2.board 90 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 91 90 89 landing || decide (bonus 91 p ≤ 1 - Generated.soko2_2Potential.boulder 90 - Generated.soko2_2Potential.hole landing + bonus 90 (change p 90 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check202 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check203 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir91_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 91 70 .northEast || decide (bonus 91 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check204 p, rfl⟩
theorem dir91_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 .northWest p = true := by
  rfl
theorem dir91_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 91 114 .southEast || decide (bonus 91 p ≤ bonus 114 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check205 p, rfl⟩
theorem dir91_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 91 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
