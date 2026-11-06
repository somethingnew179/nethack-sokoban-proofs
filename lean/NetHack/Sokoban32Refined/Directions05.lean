import NetHack.Sokoban32Refined.Directions04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir79_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 .north p = true := by
  change ((!walkGuard soko3_2.board support p 79 53 .north || decide (bonus 79 p ≤ bonus 53 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check216 p, rfl⟩
theorem dir79_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 .south p = true := by
  change ((!walkGuard soko3_2.board support p 79 105 .south || decide (bonus 79 p ≤ bonus 105 p)) && ((PreciseRolling.stayTargets soko3_2.board 105 .south).all (fun landing => !pushGuard support p 79 105 131 landing || decide (bonus 79 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 105 + bonus 105 (change p 105 (some landing)))) && (pushTargets soko3_2.board 105 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 79 105 131 landing || decide (bonus 79 p ≤ 1 - Generated.soko3_2Potential.boulder 105 - Generated.soko3_2Potential.hole landing + bonus 105 (change p 105 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check217 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check218 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir79_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 .east p = true := by
  change ((!walkGuard soko3_2.board support p 79 80 .east || decide (bonus 79 p ≤ bonus 80 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check219 p, rfl⟩
theorem dir79_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 .west p = true := by
  rfl
theorem dir79_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 79 54 .northEast || decide (bonus 79 p ≤ bonus 54 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check220 p, rfl⟩
theorem dir79_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 .northWest p = true := by
  rfl
theorem dir79_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 79 106 .southEast || decide (bonus 79 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check221 p, rfl⟩
theorem dir79_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 79 .southWest p = true := by
  rfl
theorem dir80_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 .north p = true := by
  change ((!walkGuard soko3_2.board support p 80 54 .north || decide (bonus 80 p ≤ bonus 54 p)) && ((PreciseRolling.stayTargets soko3_2.board 54 .north).all (fun landing => !pushGuard support p 80 54 28 landing || decide (bonus 80 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some landing)))) && (pushTargets soko3_2.board 54 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 80 54 28 landing || decide (bonus 80 p ≤ 1 - Generated.soko3_2Potential.boulder 54 - Generated.soko3_2Potential.hole landing + bonus 54 (change p 54 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check222 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check223 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir80_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 .south p = true := by
  change ((!walkGuard soko3_2.board support p 80 106 .south || decide (bonus 80 p ≤ bonus 106 p)) && ((PreciseRolling.stayTargets soko3_2.board 106 .south).all (fun landing => !pushGuard support p 80 106 132 landing || decide (bonus 80 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 106 + bonus 106 (change p 106 (some landing)))) && (pushTargets soko3_2.board 106 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 80 106 132 landing || decide (bonus 80 p ≤ 1 - Generated.soko3_2Potential.boulder 106 - Generated.soko3_2Potential.hole landing + bonus 106 (change p 106 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check224 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check225 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir80_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 .east p = true := by
  rfl
theorem dir80_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 .west p = true := by
  change ((!walkGuard soko3_2.board support p 80 79 .west || decide (bonus 80 p ≤ bonus 79 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check226 p, rfl⟩
theorem dir80_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 80 55 .northEast || decide (bonus 80 p ≤ bonus 55 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check227 p, rfl⟩
theorem dir80_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 80 53 .northWest || decide (bonus 80 p ≤ bonus 53 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check228 p, rfl⟩
theorem dir80_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 .southEast p = true := by
  rfl
theorem dir80_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 80 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 80 105 .southWest || decide (bonus 80 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check229 p, rfl⟩
theorem dir86_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 .north p = true := by
  change ((!walkGuard soko3_2.board support p 86 60 .north || decide (bonus 86 p ≤ bonus 60 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check230 p, rfl⟩
theorem dir86_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 .south p = true := by
  change ((!walkGuard soko3_2.board support p 86 112 .south || decide (bonus 86 p ≤ bonus 112 p)) && ((PreciseRolling.stayTargets soko3_2.board 112 .south).all (fun landing => !pushGuard support p 86 112 138 landing || decide (bonus 86 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 112 + bonus 112 (change p 112 (some landing)))) && (pushTargets soko3_2.board 112 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 86 112 138 landing || decide (bonus 86 p ≤ 1 - Generated.soko3_2Potential.boulder 112 - Generated.soko3_2Potential.hole landing + bonus 112 (change p 112 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check231 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check232 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir86_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 .east p = true := by
  rfl
theorem dir86_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 .west p = true := by
  rfl
theorem dir86_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 86 61 .northEast || decide (bonus 86 p ≤ bonus 61 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check233 p, rfl⟩
theorem dir86_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 86 59 .northWest || decide (bonus 86 p ≤ bonus 59 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check234 p, rfl⟩
theorem dir86_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 86 113 .southEast || decide (bonus 86 p ≤ bonus 113 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check235 p, rfl⟩
theorem dir86_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 86 .southWest p = true := by
  rfl
theorem dir88_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 .north p = true := by
  change ((!walkGuard soko3_2.board support p 88 62 .north || decide (bonus 88 p ≤ bonus 62 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check236 p, rfl⟩
theorem dir88_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 .south p = true := by
  change ((!walkGuard soko3_2.board support p 88 114 .south || decide (bonus 88 p ≤ bonus 114 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check237 p, rfl⟩
theorem dir88_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 .east p = true := by
  rfl
theorem dir88_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 .west p = true := by
  rfl
theorem dir88_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 .northEast p = true := by
  rfl
theorem dir88_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 88 61 .northWest || decide (bonus 88 p ≤ bonus 61 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check238 p, rfl⟩
theorem dir88_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 .southEast p = true := by
  rfl
theorem dir88_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 88 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 88 113 .southWest || decide (bonus 88 p ≤ bonus 113 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check239 p, rfl⟩
theorem dir94_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 .north p = true := by
  change ((!walkGuard soko3_2.board support p 94 68 .north || decide (bonus 94 p ≤ bonus 68 p)) && ((PreciseRolling.stayTargets soko3_2.board 68 .north).all (fun landing => !pushGuard support p 94 68 42 landing || decide (bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 68 + bonus 68 (change p 68 (some landing)))) && (pushTargets soko3_2.board 68 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 94 68 42 landing || decide (bonus 94 p ≤ 1 - Generated.soko3_2Potential.boulder 68 - Generated.soko3_2Potential.hole landing + bonus 68 (change p 68 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check240 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check241 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir94_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 .south p = true := by
  change ((!walkGuard soko3_2.board support p 94 120 .south || decide (bonus 94 p ≤ bonus 120 p)) && ((PreciseRolling.stayTargets soko3_2.board 120 .south).all (fun landing => !pushGuard support p 94 120 146 landing || decide (bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 120 + bonus 120 (change p 120 (some landing)))) && (pushTargets soko3_2.board 120 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 94 120 146 landing || decide (bonus 94 p ≤ 1 - Generated.soko3_2Potential.boulder 120 - Generated.soko3_2Potential.hole landing + bonus 120 (change p 120 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check242 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check243 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir94_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 .east p = true := by
  change ((!walkGuard soko3_2.board support p 94 95 .east || decide (bonus 94 p ≤ bonus 95 p)) && ((PreciseRolling.stayTargets soko3_2.board 95 .east).all (fun landing => !pushGuard support p 94 95 96 landing || decide (bonus 94 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some landing)))) && (pushTargets soko3_2.board 95 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 94 95 96 landing || decide (bonus 94 p ≤ 1 - Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.hole landing + bonus 95 (change p 95 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check244 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check245 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir94_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 .west p = true := by
  rfl
theorem dir94_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 94 69 .northEast || decide (bonus 94 p ≤ bonus 69 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check246 p, rfl⟩
theorem dir94_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 .northWest p = true := by
  rfl
theorem dir94_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 94 121 .southEast || decide (bonus 94 p ≤ bonus 121 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check247 p, rfl⟩
theorem dir94_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 94 .southWest p = true := by
  rfl
theorem dir95_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 .north p = true := by
  change ((!walkGuard soko3_2.board support p 95 69 .north || decide (bonus 95 p ≤ bonus 69 p)) && ((PreciseRolling.stayTargets soko3_2.board 69 .north).all (fun landing => !pushGuard support p 95 69 43 landing || decide (bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some landing)))) && (pushTargets soko3_2.board 69 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 95 69 43 landing || decide (bonus 95 p ≤ 1 - Generated.soko3_2Potential.boulder 69 - Generated.soko3_2Potential.hole landing + bonus 69 (change p 69 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check248 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check249 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir95_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 .south p = true := by
  change ((!walkGuard soko3_2.board support p 95 121 .south || decide (bonus 95 p ≤ bonus 121 p)) && ((PreciseRolling.stayTargets soko3_2.board 121 .south).all (fun landing => !pushGuard support p 95 121 147 landing || decide (bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some landing)))) && (pushTargets soko3_2.board 121 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 95 121 147 landing || decide (bonus 95 p ≤ 1 - Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.hole landing + bonus 121 (change p 121 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check250 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check251 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir95_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 .east p = true := by
  change ((!walkGuard soko3_2.board support p 95 96 .east || decide (bonus 95 p ≤ bonus 96 p)) && ((PreciseRolling.stayTargets soko3_2.board 96 .east).all (fun landing => !pushGuard support p 95 96 97 landing || decide (bonus 95 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some landing)))) && (pushTargets soko3_2.board 96 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 95 96 97 landing || decide (bonus 95 p ≤ 1 - Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.hole landing + bonus 96 (change p 96 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check252 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check253 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir95_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 .west p = true := by
  change ((!walkGuard soko3_2.board support p 95 94 .west || decide (bonus 95 p ≤ bonus 94 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check254 p, rfl⟩
theorem dir95_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 95 70 .northEast || decide (bonus 95 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check255 p, rfl⟩
theorem dir95_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 95 68 .northWest || decide (bonus 95 p ≤ bonus 68 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check256 p, rfl⟩
theorem dir95_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 95 122 .southEast || decide (bonus 95 p ≤ bonus 122 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check257 p, rfl⟩
theorem dir95_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 95 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 95 120 .southWest || decide (bonus 95 p ≤ bonus 120 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check258 p, rfl⟩
end NetHack.Sokoban32Refined
