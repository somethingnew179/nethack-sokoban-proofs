import NetHack.Sokoban22Refined85.Directions00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir46_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 .north p = true := by
  rfl
theorem dir46_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 .south p = true := by
  rfl
theorem dir46_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 .east p = true := by
  change ((!walkGuard soko2_2.board support p 46 47 .east || decide (bonus 46 p ≤ bonus 47 p)) && ((PreciseRolling.stayTargets soko2_2.board 47 .east).all (fun landing => !pushGuard support p 46 47 48 landing || decide (bonus 46 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some landing)))) && (pushTargets soko2_2.board 47 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 46 47 48 landing || decide (bonus 46 p ≤ 1 - Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.hole landing + bonus 47 (change p 47 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check32 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check33 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir46_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 .west p = true := by
  change ((!walkGuard soko2_2.board support p 46 45 .west || decide (bonus 46 p ≤ bonus 45 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check34 p, rfl⟩
theorem dir46_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 46 25 .northEast || decide (bonus 46 p ≤ bonus 25 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check35 p, rfl⟩
theorem dir46_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 .northWest p = true := by
  rfl
theorem dir46_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 46 69 .southEast || decide (bonus 46 p ≤ bonus 69 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check36 p, rfl⟩
theorem dir46_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 46 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 46 67 .southWest || decide (bonus 46 p ≤ bonus 67 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check37 p, rfl⟩
theorem dir47_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 .north p = true := by
  change ((!walkGuard soko2_2.board support p 47 25 .north || decide (bonus 47 p ≤ bonus 25 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check38 p, rfl⟩
theorem dir47_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 .south p = true := by
  change ((!walkGuard soko2_2.board support p 47 69 .south || decide (bonus 47 p ≤ bonus 69 p)) && ((PreciseRolling.stayTargets soko2_2.board 69 .south).all (fun landing => !pushGuard support p 47 69 91 landing || decide (bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 69 + bonus 69 (change p 69 (some landing)))) && (pushTargets soko2_2.board 69 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 47 69 91 landing || decide (bonus 47 p ≤ 1 - Generated.soko2_2Potential.boulder 69 - Generated.soko2_2Potential.hole landing + bonus 69 (change p 69 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check39 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check40 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir47_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 .east p = true := by
  change ((!walkGuard soko2_2.board support p 47 48 .east || decide (bonus 47 p ≤ bonus 48 p)) && ((PreciseRolling.stayTargets soko2_2.board 48 .east).all (fun landing => !pushGuard support p 47 48 49 landing || decide (bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 48 + bonus 48 (change p 48 (some landing)))) && (pushTargets soko2_2.board 48 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 47 48 49 landing || decide (bonus 47 p ≤ 1 - Generated.soko2_2Potential.boulder 48 - Generated.soko2_2Potential.hole landing + bonus 48 (change p 48 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check41 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check42 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir47_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 .west p = true := by
  change ((!walkGuard soko2_2.board support p 47 46 .west || decide (bonus 47 p ≤ bonus 46 p)) && ((PreciseRolling.stayTargets soko2_2.board 46 .west).all (fun landing => !pushGuard support p 47 46 45 landing || decide (bonus 47 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 46 + bonus 46 (change p 46 (some landing)))) && (pushTargets soko2_2.board 46 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 47 46 45 landing || decide (bonus 47 p ≤ 1 - Generated.soko2_2Potential.boulder 46 - Generated.soko2_2Potential.hole landing + bonus 46 (change p 46 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check43 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check44 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir47_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 .northEast p = true := by
  rfl
theorem dir47_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 .northWest p = true := by
  rfl
theorem dir47_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 47 70 .southEast || decide (bonus 47 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check45 p, rfl⟩
theorem dir47_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 47 .southWest p = true := by
  rfl
theorem dir48_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 .north p = true := by
  rfl
theorem dir48_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 .south p = true := by
  change ((!walkGuard soko2_2.board support p 48 70 .south || decide (bonus 48 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check46 p, rfl⟩
theorem dir48_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 .east p = true := by
  change ((!walkGuard soko2_2.board support p 48 49 .east || decide (bonus 48 p ≤ bonus 49 p)) && ((PreciseRolling.stayTargets soko2_2.board 49 .east).all (fun landing => !pushGuard support p 48 49 50 landing || decide (bonus 48 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some landing)))) && (pushTargets soko2_2.board 49 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 48 49 50 landing || decide (bonus 48 p ≤ 1 - Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.hole landing + bonus 49 (change p 49 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check47 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check48 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir48_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 .west p = true := by
  change ((!walkGuard soko2_2.board support p 48 47 .west || decide (bonus 48 p ≤ bonus 47 p)) && ((PreciseRolling.stayTargets soko2_2.board 47 .west).all (fun landing => !pushGuard support p 48 47 46 landing || decide (bonus 48 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some landing)))) && (pushTargets soko2_2.board 47 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 48 47 46 landing || decide (bonus 48 p ≤ 1 - Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.hole landing + bonus 47 (change p 47 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check49 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check50 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir48_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 48 27 .northEast || decide (bonus 48 p ≤ bonus 27 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check51 p, rfl⟩
theorem dir48_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 48 25 .northWest || decide (bonus 48 p ≤ bonus 25 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check52 p, rfl⟩
theorem dir48_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 48 71 .southEast || decide (bonus 48 p ≤ bonus 71 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check53 p, rfl⟩
theorem dir48_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 48 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 48 69 .southWest || decide (bonus 48 p ≤ bonus 69 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check54 p, rfl⟩
theorem dir49_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 .north p = true := by
  change ((!walkGuard soko2_2.board support p 49 27 .north || decide (bonus 49 p ≤ bonus 27 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check55 p, rfl⟩
theorem dir49_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 .south p = true := by
  change ((!walkGuard soko2_2.board support p 49 71 .south || decide (bonus 49 p ≤ bonus 71 p)) && ((PreciseRolling.stayTargets soko2_2.board 71 .south).all (fun landing => !pushGuard support p 49 71 93 landing || decide (bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 71 + bonus 71 (change p 71 (some landing)))) && (pushTargets soko2_2.board 71 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 49 71 93 landing || decide (bonus 49 p ≤ 1 - Generated.soko2_2Potential.boulder 71 - Generated.soko2_2Potential.hole landing + bonus 71 (change p 71 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check56 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check57 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir49_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 .east p = true := by
  change ((!walkGuard soko2_2.board support p 49 50 .east || decide (bonus 49 p ≤ bonus 50 p)) && ((PreciseRolling.stayTargets soko2_2.board 50 .east).all (fun landing => !pushGuard support p 49 50 51 landing || decide (bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 50 + bonus 50 (change p 50 (some landing)))) && (pushTargets soko2_2.board 50 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 49 50 51 landing || decide (bonus 49 p ≤ 1 - Generated.soko2_2Potential.boulder 50 - Generated.soko2_2Potential.hole landing + bonus 50 (change p 50 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check58 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check59 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir49_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 .west p = true := by
  change ((!walkGuard soko2_2.board support p 49 48 .west || decide (bonus 49 p ≤ bonus 48 p)) && ((PreciseRolling.stayTargets soko2_2.board 48 .west).all (fun landing => !pushGuard support p 49 48 47 landing || decide (bonus 49 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 48 + bonus 48 (change p 48 (some landing)))) && (pushTargets soko2_2.board 48 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 49 48 47 landing || decide (bonus 49 p ≤ 1 - Generated.soko2_2Potential.boulder 48 - Generated.soko2_2Potential.hole landing + bonus 48 (change p 48 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check60 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check61 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir49_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 49 28 .northEast || decide (bonus 49 p ≤ bonus 28 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check62 p, rfl⟩
theorem dir49_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 .northWest p = true := by
  rfl
theorem dir49_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 .southEast p = true := by
  rfl
theorem dir49_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 49 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 49 70 .southWest || decide (bonus 49 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check63 p, rfl⟩
theorem dir50_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 .north p = true := by
  change ((!walkGuard soko2_2.board support p 50 28 .north || decide (bonus 50 p ≤ bonus 28 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check64 p, rfl⟩
theorem dir50_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 .south p = true := by
  rfl
theorem dir50_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 .east p = true := by
  change ((!walkGuard soko2_2.board support p 50 51 .east || decide (bonus 50 p ≤ bonus 51 p)) && ((PreciseRolling.stayTargets soko2_2.board 51 .east).all (fun landing => !pushGuard support p 50 51 52 landing || decide (bonus 50 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some landing)))) && (pushTargets soko2_2.board 51 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 50 51 52 landing || decide (bonus 50 p ≤ 1 - Generated.soko2_2Potential.boulder 51 - Generated.soko2_2Potential.hole landing + bonus 51 (change p 51 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check65 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check66 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir50_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 .west p = true := by
  change ((!walkGuard soko2_2.board support p 50 49 .west || decide (bonus 50 p ≤ bonus 49 p)) && ((PreciseRolling.stayTargets soko2_2.board 49 .west).all (fun landing => !pushGuard support p 50 49 48 landing || decide (bonus 50 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some landing)))) && (pushTargets soko2_2.board 49 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 50 49 48 landing || decide (bonus 50 p ≤ 1 - Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.hole landing + bonus 49 (change p 49 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check67 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check68 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir50_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 50 29 .northEast || decide (bonus 50 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check69 p, rfl⟩
theorem dir50_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 50 27 .northWest || decide (bonus 50 p ≤ bonus 27 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check70 p, rfl⟩
theorem dir50_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 50 73 .southEast || decide (bonus 50 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check71 p, rfl⟩
theorem dir50_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 50 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 50 71 .southWest || decide (bonus 50 p ≤ bonus 71 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check72 p, rfl⟩
theorem dir51_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 .north p = true := by
  change ((!walkGuard soko2_2.board support p 51 29 .north || decide (bonus 51 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check73 p, rfl⟩
theorem dir51_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 .south p = true := by
  change ((!walkGuard soko2_2.board support p 51 73 .south || decide (bonus 51 p ≤ bonus 73 p)) && ((PreciseRolling.stayTargets soko2_2.board 73 .south).all (fun landing => !pushGuard support p 51 73 95 landing || decide (bonus 51 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 73 + bonus 73 (change p 73 (some landing)))) && (pushTargets soko2_2.board 73 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 51 73 95 landing || decide (bonus 51 p ≤ 1 - Generated.soko2_2Potential.boulder 73 - Generated.soko2_2Potential.hole landing + bonus 73 (change p 73 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check74 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check75 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir51_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 .east p = true := by
  change ((!walkGuard soko2_2.board support p 51 52 .east || decide (bonus 51 p ≤ bonus 52 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check76 p, rfl⟩
theorem dir51_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 .west p = true := by
  change ((!walkGuard soko2_2.board support p 51 50 .west || decide (bonus 51 p ≤ bonus 50 p)) && ((PreciseRolling.stayTargets soko2_2.board 50 .west).all (fun landing => !pushGuard support p 51 50 49 landing || decide (bonus 51 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 50 + bonus 50 (change p 50 (some landing)))) && (pushTargets soko2_2.board 50 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 51 50 49 landing || decide (bonus 51 p ≤ 1 - Generated.soko2_2Potential.boulder 50 - Generated.soko2_2Potential.hole landing + bonus 50 (change p 50 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check77 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check78 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir51_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 51 30 .northEast || decide (bonus 51 p ≤ bonus 30 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check79 p, rfl⟩
theorem dir51_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 51 28 .northWest || decide (bonus 51 p ≤ bonus 28 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check80 p, rfl⟩
theorem dir51_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 51 74 .southEast || decide (bonus 51 p ≤ bonus 74 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check81 p, rfl⟩
theorem dir51_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 51 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
