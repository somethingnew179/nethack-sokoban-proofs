import NetHack.Sokoban22Refined85.Directions04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir93_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 .north p = true := by
  change ((!walkGuard soko2_2.board support p 93 71 .north || decide (bonus 93 p ≤ bonus 71 p)) && ((PreciseRolling.stayTargets soko2_2.board 71 .north).all (fun landing => !pushGuard support p 93 71 49 landing || decide (bonus 93 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 71 + bonus 71 (change p 71 (some landing)))) && (pushTargets soko2_2.board 71 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 93 71 49 landing || decide (bonus 93 p ≤ 1 - Generated.soko2_2Potential.boulder 71 - Generated.soko2_2Potential.hole landing + bonus 71 (change p 71 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check206 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check207 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir93_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 .south p = true := by
  change ((!walkGuard soko2_2.board support p 93 115 .south || decide (bonus 93 p ≤ bonus 115 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check208 p, rfl⟩
theorem dir93_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 .east p = true := by
  change ((!walkGuard soko2_2.board support p 93 94 .east || decide (bonus 93 p ≤ bonus 94 p)) && ((PreciseRolling.stayTargets soko2_2.board 94 .east).all (fun landing => !pushGuard support p 93 94 95 landing || decide (bonus 93 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 94 + bonus 94 (change p 94 (some landing)))) && (pushTargets soko2_2.board 94 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 93 94 95 landing || decide (bonus 93 p ≤ 1 - Generated.soko2_2Potential.boulder 94 - Generated.soko2_2Potential.hole landing + bonus 94 (change p 94 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check209 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check210 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir93_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 .west p = true := by
  rfl
theorem dir93_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 .northEast p = true := by
  rfl
theorem dir93_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 93 70 .northWest || decide (bonus 93 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check211 p, rfl⟩
theorem dir93_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 93 116 .southEast || decide (bonus 93 p ≤ bonus 116 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check212 p, rfl⟩
theorem dir93_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 93 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 93 114 .southWest || decide (bonus 93 p ≤ bonus 114 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check213 p, rfl⟩
theorem dir94_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 .north p = true := by
  rfl
theorem dir94_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 .south p = true := by
  change ((!walkGuard soko2_2.board support p 94 116 .south || decide (bonus 94 p ≤ bonus 116 p)) && ((PreciseRolling.stayTargets soko2_2.board 116 .south).all (fun landing => !pushGuard support p 94 116 138 landing || decide (bonus 94 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 116 + bonus 116 (change p 116 (some landing)))) && (pushTargets soko2_2.board 116 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 94 116 138 landing || decide (bonus 94 p ≤ 1 - Generated.soko2_2Potential.boulder 116 - Generated.soko2_2Potential.hole landing + bonus 116 (change p 116 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check214 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check215 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir94_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 .east p = true := by
  change ((!walkGuard soko2_2.board support p 94 95 .east || decide (bonus 94 p ≤ bonus 95 p)) && ((PreciseRolling.stayTargets soko2_2.board 95 .east).all (fun landing => !pushGuard support p 94 95 96 landing || decide (bonus 94 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 95 + bonus 95 (change p 95 (some landing)))) && (pushTargets soko2_2.board 95 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 94 95 96 landing || decide (bonus 94 p ≤ 1 - Generated.soko2_2Potential.boulder 95 - Generated.soko2_2Potential.hole landing + bonus 95 (change p 95 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check216 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check217 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir94_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 .west p = true := by
  change ((!walkGuard soko2_2.board support p 94 93 .west || decide (bonus 94 p ≤ bonus 93 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check218 p, rfl⟩
theorem dir94_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 94 73 .northEast || decide (bonus 94 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check219 p, rfl⟩
theorem dir94_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 94 71 .northWest || decide (bonus 94 p ≤ bonus 71 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check220 p, rfl⟩
theorem dir94_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 .southEast p = true := by
  rfl
theorem dir94_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 94 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 94 115 .southWest || decide (bonus 94 p ≤ bonus 115 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check221 p, rfl⟩
theorem dir95_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 .north p = true := by
  change ((!walkGuard soko2_2.board support p 95 73 .north || decide (bonus 95 p ≤ bonus 73 p)) && ((PreciseRolling.stayTargets soko2_2.board 73 .north).all (fun landing => !pushGuard support p 95 73 51 landing || decide (bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 73 + bonus 73 (change p 73 (some landing)))) && (pushTargets soko2_2.board 73 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 95 73 51 landing || decide (bonus 95 p ≤ 1 - Generated.soko2_2Potential.boulder 73 - Generated.soko2_2Potential.hole landing + bonus 73 (change p 73 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check222 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check223 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir95_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 .south p = true := by
  rfl
theorem dir95_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 .east p = true := by
  change ((!walkGuard soko2_2.board support p 95 96 .east || decide (bonus 95 p ≤ bonus 96 p)) && ((PreciseRolling.stayTargets soko2_2.board 96 .east).all (fun landing => !pushGuard support p 95 96 97 landing || decide (bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some landing)))) && (pushTargets soko2_2.board 96 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 95 96 97 landing || decide (bonus 95 p ≤ 1 - Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.hole landing + bonus 96 (change p 96 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check224 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check225 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir95_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 .west p = true := by
  change ((!walkGuard soko2_2.board support p 95 94 .west || decide (bonus 95 p ≤ bonus 94 p)) && ((PreciseRolling.stayTargets soko2_2.board 94 .west).all (fun landing => !pushGuard support p 95 94 93 landing || decide (bonus 95 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 94 + bonus 94 (change p 94 (some landing)))) && (pushTargets soko2_2.board 94 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 95 94 93 landing || decide (bonus 95 p ≤ 1 - Generated.soko2_2Potential.boulder 94 - Generated.soko2_2Potential.hole landing + bonus 94 (change p 94 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check226 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check227 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir95_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 95 74 .northEast || decide (bonus 95 p ≤ bonus 74 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check228 p, rfl⟩
theorem dir95_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 .northWest p = true := by
  rfl
theorem dir95_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 95 118 .southEast || decide (bonus 95 p ≤ bonus 118 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check229 p, rfl⟩
theorem dir95_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 95 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 95 116 .southWest || decide (bonus 95 p ≤ bonus 116 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check230 p, rfl⟩
theorem dir96_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 .north p = true := by
  change ((!walkGuard soko2_2.board support p 96 74 .north || decide (bonus 96 p ≤ bonus 74 p)) && ((PreciseRolling.stayTargets soko2_2.board 74 .north).all (fun landing => !pushGuard support p 96 74 52 landing || decide (bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 74 + bonus 74 (change p 74 (some landing)))) && (pushTargets soko2_2.board 74 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 96 74 52 landing || decide (bonus 96 p ≤ 1 - Generated.soko2_2Potential.boulder 74 - Generated.soko2_2Potential.hole landing + bonus 74 (change p 74 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check231 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check232 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir96_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 .south p = true := by
  change ((!walkGuard soko2_2.board support p 96 118 .south || decide (bonus 96 p ≤ bonus 118 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check233 p, rfl⟩
theorem dir96_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 .east p = true := by
  change ((!walkGuard soko2_2.board support p 96 97 .east || decide (bonus 96 p ≤ bonus 97 p)) && ((PreciseRolling.stayTargets soko2_2.board 97 .east).all (fun landing => !pushGuard support p 96 97 98 landing || decide (bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 97 + bonus 97 (change p 97 (some landing)))) && (pushTargets soko2_2.board 97 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 96 97 98 landing || decide (bonus 96 p ≤ 1 - Generated.soko2_2Potential.boulder 97 - Generated.soko2_2Potential.hole landing + bonus 97 (change p 97 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check234 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check235 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir96_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 .west p = true := by
  change ((!walkGuard soko2_2.board support p 96 95 .west || decide (bonus 96 p ≤ bonus 95 p)) && ((PreciseRolling.stayTargets soko2_2.board 95 .west).all (fun landing => !pushGuard support p 96 95 94 landing || decide (bonus 96 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 95 + bonus 95 (change p 95 (some landing)))) && (pushTargets soko2_2.board 95 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 96 95 94 landing || decide (bonus 96 p ≤ 1 - Generated.soko2_2Potential.boulder 95 - Generated.soko2_2Potential.hole landing + bonus 95 (change p 95 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check236 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check237 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir96_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 .northEast p = true := by
  rfl
theorem dir96_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 96 73 .northWest || decide (bonus 96 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check238 p, rfl⟩
theorem dir96_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 96 119 .southEast || decide (bonus 96 p ≤ bonus 119 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check239 p, rfl⟩
theorem dir96_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 96 .southWest p = true := by
  rfl
theorem dir97_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 .north p = true := by
  rfl
theorem dir97_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 .south p = true := by
  change ((!walkGuard soko2_2.board support p 97 119 .south || decide (bonus 97 p ≤ bonus 119 p)) && ((PreciseRolling.stayTargets soko2_2.board 119 .south).all (fun landing => !pushGuard support p 97 119 141 landing || decide (bonus 97 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some landing)))) && (pushTargets soko2_2.board 119 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 97 119 141 landing || decide (bonus 97 p ≤ 1 - Generated.soko2_2Potential.boulder 119 - Generated.soko2_2Potential.hole landing + bonus 119 (change p 119 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check240 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check241 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir97_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 .east p = true := by
  change ((!walkGuard soko2_2.board support p 97 98 .east || decide (bonus 97 p ≤ bonus 98 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check242 p, rfl⟩
theorem dir97_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 .west p = true := by
  change ((!walkGuard soko2_2.board support p 97 96 .west || decide (bonus 97 p ≤ bonus 96 p)) && ((PreciseRolling.stayTargets soko2_2.board 96 .west).all (fun landing => !pushGuard support p 97 96 95 landing || decide (bonus 97 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some landing)))) && (pushTargets soko2_2.board 96 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 97 96 95 landing || decide (bonus 97 p ≤ 1 - Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.hole landing + bonus 96 (change p 96 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check243 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check244 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir97_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 97 76 .northEast || decide (bonus 97 p ≤ bonus 76 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check245 p, rfl⟩
theorem dir97_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 97 74 .northWest || decide (bonus 97 p ≤ bonus 74 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check246 p, rfl⟩
theorem dir97_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 97 120 .southEast || decide (bonus 97 p ≤ bonus 120 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check247 p, rfl⟩
theorem dir97_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 97 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 97 118 .southWest || decide (bonus 97 p ≤ bonus 118 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check248 p, rfl⟩
theorem dir98_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 .north p = true := by
  change ((!walkGuard soko2_2.board support p 98 76 .north || decide (bonus 98 p ≤ bonus 76 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check249 p, rfl⟩
theorem dir98_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 .south p = true := by
  change ((!walkGuard soko2_2.board support p 98 120 .south || decide (bonus 98 p ≤ bonus 120 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check250 p, rfl⟩
theorem dir98_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 .east p = true := by
  rfl
theorem dir98_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 .west p = true := by
  change ((!walkGuard soko2_2.board support p 98 97 .west || decide (bonus 98 p ≤ bonus 97 p)) && ((PreciseRolling.stayTargets soko2_2.board 97 .west).all (fun landing => !pushGuard support p 98 97 96 landing || decide (bonus 98 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 97 + bonus 97 (change p 97 (some landing)))) && (pushTargets soko2_2.board 97 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 98 97 96 landing || decide (bonus 98 p ≤ 1 - Generated.soko2_2Potential.boulder 97 - Generated.soko2_2Potential.hole landing + bonus 97 (change p 97 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check251 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check252 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir98_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 .northEast p = true := by
  rfl
theorem dir98_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 .northWest p = true := by
  rfl
theorem dir98_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 .southEast p = true := by
  rfl
theorem dir98_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 98 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 98 119 .southWest || decide (bonus 98 p ≤ bonus 119 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check253 p, rfl⟩
end NetHack.Sokoban22Refined85
