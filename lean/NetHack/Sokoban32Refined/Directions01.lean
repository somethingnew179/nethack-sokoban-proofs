import NetHack.Sokoban32Refined.Directions00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir46_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 .north p = true := by
  rfl
theorem dir46_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 .south p = true := by
  change ((!walkGuard soko3_2.board support p 46 72 .south || decide (bonus 46 p ≤ bonus 72 p)) && ((PreciseRolling.stayTargets soko3_2.board 72 .south).all (fun landing => !pushGuard support p 46 72 98 landing || decide (bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some landing)))) && (pushTargets soko3_2.board 72 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 46 72 98 landing || decide (bonus 46 p ≤ 1 - Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.hole landing + bonus 72 (change p 72 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check37 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check38 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir46_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 .east p = true := by
  change ((!walkGuard soko3_2.board support p 46 47 .east || decide (bonus 46 p ≤ bonus 47 p)) && ((PreciseRolling.stayTargets soko3_2.board 47 .east).all (fun landing => !pushGuard support p 46 47 48 landing || decide (bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 47 + bonus 47 (change p 47 (some landing)))) && (pushTargets soko3_2.board 47 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 46 47 48 landing || decide (bonus 46 p ≤ 1 - Generated.soko3_2Potential.boulder 47 - Generated.soko3_2Potential.hole landing + bonus 47 (change p 47 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check39 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check40 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir46_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 .west p = true := by
  change ((!walkGuard soko3_2.board support p 46 45 .west || decide (bonus 46 p ≤ bonus 45 p)) && ((PreciseRolling.stayTargets soko3_2.board 45 .west).all (fun landing => !pushGuard support p 46 45 44 landing || decide (bonus 46 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 45 + bonus 45 (change p 45 (some landing)))) && (pushTargets soko3_2.board 45 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 46 45 44 landing || decide (bonus 46 p ≤ 1 - Generated.soko3_2Potential.boulder 45 - Generated.soko3_2Potential.hole landing + bonus 45 (change p 45 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check41 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check42 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir46_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 .northEast p = true := by
  rfl
theorem dir46_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 .northWest p = true := by
  rfl
theorem dir46_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 46 73 .southEast || decide (bonus 46 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check43 p, rfl⟩
theorem dir46_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 46 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 46 71 .southWest || decide (bonus 46 p ≤ bonus 71 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check44 p, rfl⟩
theorem dir47_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 .north p = true := by
  rfl
theorem dir47_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 .south p = true := by
  change ((!walkGuard soko3_2.board support p 47 73 .south || decide (bonus 47 p ≤ bonus 73 p)) && ((PreciseRolling.stayTargets soko3_2.board 73 .south).all (fun landing => !pushGuard support p 47 73 99 landing || decide (bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some landing)))) && (pushTargets soko3_2.board 73 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 47 73 99 landing || decide (bonus 47 p ≤ 1 - Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.hole landing + bonus 73 (change p 73 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check45 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check46 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir47_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 .east p = true := by
  change ((!walkGuard soko3_2.board support p 47 48 .east || decide (bonus 47 p ≤ bonus 48 p)) && ((PreciseRolling.stayTargets soko3_2.board 48 .east).all (fun landing => !pushGuard support p 47 48 49 landing || decide (bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 48 + bonus 48 (change p 48 (some landing)))) && (pushTargets soko3_2.board 48 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 47 48 49 landing || decide (bonus 47 p ≤ 1 - Generated.soko3_2Potential.boulder 48 - Generated.soko3_2Potential.hole landing + bonus 48 (change p 48 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check47 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check48 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir47_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 .west p = true := by
  change ((!walkGuard soko3_2.board support p 47 46 .west || decide (bonus 47 p ≤ bonus 46 p)) && ((PreciseRolling.stayTargets soko3_2.board 46 .west).all (fun landing => !pushGuard support p 47 46 45 landing || decide (bonus 47 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 46 + bonus 46 (change p 46 (some landing)))) && (pushTargets soko3_2.board 46 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 47 46 45 landing || decide (bonus 47 p ≤ 1 - Generated.soko3_2Potential.boulder 46 - Generated.soko3_2Potential.hole landing + bonus 46 (change p 46 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check49 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check50 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir47_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 .northEast p = true := by
  rfl
theorem dir47_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 .northWest p = true := by
  rfl
theorem dir47_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 47 74 .southEast || decide (bonus 47 p ≤ bonus 74 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check51 p, rfl⟩
theorem dir47_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 47 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 47 72 .southWest || decide (bonus 47 p ≤ bonus 72 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check52 p, rfl⟩
theorem dir48_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 .north p = true := by
  rfl
theorem dir48_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 .south p = true := by
  change ((!walkGuard soko3_2.board support p 48 74 .south || decide (bonus 48 p ≤ bonus 74 p)) && ((PreciseRolling.stayTargets soko3_2.board 74 .south).all (fun landing => !pushGuard support p 48 74 100 landing || decide (bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some landing)))) && (pushTargets soko3_2.board 74 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 48 74 100 landing || decide (bonus 48 p ≤ 1 - Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.hole landing + bonus 74 (change p 74 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check53 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check54 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir48_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 .east p = true := by
  change ((!walkGuard soko3_2.board support p 48 49 .east || decide (bonus 48 p ≤ bonus 49 p)) && ((PreciseRolling.stayTargets soko3_2.board 49 .east).all (fun landing => !pushGuard support p 48 49 50 landing || decide (bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 49 + bonus 49 (change p 49 (some landing)))) && (pushTargets soko3_2.board 49 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 48 49 50 landing || decide (bonus 48 p ≤ 1 - Generated.soko3_2Potential.boulder 49 - Generated.soko3_2Potential.hole landing + bonus 49 (change p 49 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check55 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check56 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir48_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 .west p = true := by
  change ((!walkGuard soko3_2.board support p 48 47 .west || decide (bonus 48 p ≤ bonus 47 p)) && ((PreciseRolling.stayTargets soko3_2.board 47 .west).all (fun landing => !pushGuard support p 48 47 46 landing || decide (bonus 48 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 47 + bonus 47 (change p 47 (some landing)))) && (pushTargets soko3_2.board 47 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 48 47 46 landing || decide (bonus 48 p ≤ 1 - Generated.soko3_2Potential.boulder 47 - Generated.soko3_2Potential.hole landing + bonus 47 (change p 47 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check57 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check58 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir48_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 .northEast p = true := by
  rfl
theorem dir48_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 .northWest p = true := by
  rfl
theorem dir48_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 48 75 .southEast || decide (bonus 48 p ≤ bonus 75 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check59 p, rfl⟩
theorem dir48_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 48 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 48 73 .southWest || decide (bonus 48 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check60 p, rfl⟩
theorem dir49_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 .north p = true := by
  rfl
theorem dir49_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 .south p = true := by
  change ((!walkGuard soko3_2.board support p 49 75 .south || decide (bonus 49 p ≤ bonus 75 p)) && ((PreciseRolling.stayTargets soko3_2.board 75 .south).all (fun landing => !pushGuard support p 49 75 101 landing || decide (bonus 49 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some landing)))) && (pushTargets soko3_2.board 75 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 49 75 101 landing || decide (bonus 49 p ≤ 1 - Generated.soko3_2Potential.boulder 75 - Generated.soko3_2Potential.hole landing + bonus 75 (change p 75 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check61 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check62 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir49_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 .east p = true := by
  change ((!walkGuard soko3_2.board support p 49 50 .east || decide (bonus 49 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check63 p, rfl⟩
theorem dir49_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 .west p = true := by
  change ((!walkGuard soko3_2.board support p 49 48 .west || decide (bonus 49 p ≤ bonus 48 p)) && ((PreciseRolling.stayTargets soko3_2.board 48 .west).all (fun landing => !pushGuard support p 49 48 47 landing || decide (bonus 49 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 48 + bonus 48 (change p 48 (some landing)))) && (pushTargets soko3_2.board 48 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 49 48 47 landing || decide (bonus 49 p ≤ 1 - Generated.soko3_2Potential.boulder 48 - Generated.soko3_2Potential.hole landing + bonus 48 (change p 48 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check64 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check65 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir49_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 .northEast p = true := by
  rfl
theorem dir49_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 .northWest p = true := by
  rfl
theorem dir49_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 49 76 .southEast || decide (bonus 49 p ≤ bonus 76 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check66 p, rfl⟩
theorem dir49_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 49 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 49 74 .southWest || decide (bonus 49 p ≤ bonus 74 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check67 p, rfl⟩
theorem dir50_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 .north p = true := by
  rfl
theorem dir50_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 .south p = true := by
  change ((!walkGuard soko3_2.board support p 50 76 .south || decide (bonus 50 p ≤ bonus 76 p)) && ((PreciseRolling.stayTargets soko3_2.board 76 .south).all (fun landing => !pushGuard support p 50 76 102 landing || decide (bonus 50 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 76 + bonus 76 (change p 76 (some landing)))) && (pushTargets soko3_2.board 76 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 50 76 102 landing || decide (bonus 50 p ≤ 1 - Generated.soko3_2Potential.boulder 76 - Generated.soko3_2Potential.hole landing + bonus 76 (change p 76 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check68 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check69 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir50_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 .east p = true := by
  rfl
theorem dir50_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 .west p = true := by
  change ((!walkGuard soko3_2.board support p 50 49 .west || decide (bonus 50 p ≤ bonus 49 p)) && ((PreciseRolling.stayTargets soko3_2.board 49 .west).all (fun landing => !pushGuard support p 50 49 48 landing || decide (bonus 50 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 49 + bonus 49 (change p 49 (some landing)))) && (pushTargets soko3_2.board 49 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 50 49 48 landing || decide (bonus 50 p ≤ 1 - Generated.soko3_2Potential.boulder 49 - Generated.soko3_2Potential.hole landing + bonus 49 (change p 49 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check70 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check71 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir50_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 .northEast p = true := by
  rfl
theorem dir50_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 .northWest p = true := by
  rfl
theorem dir50_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 .southEast p = true := by
  rfl
theorem dir50_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 50 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 50 75 .southWest || decide (bonus 50 p ≤ bonus 75 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check72 p, rfl⟩
theorem dir53_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 .north p = true := by
  rfl
theorem dir53_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 .south p = true := by
  change ((!walkGuard soko3_2.board support p 53 79 .south || decide (bonus 53 p ≤ bonus 79 p)) && ((PreciseRolling.stayTargets soko3_2.board 79 .south).all (fun landing => !pushGuard support p 53 79 105 landing || decide (bonus 53 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 79 + bonus 79 (change p 79 (some landing)))) && (pushTargets soko3_2.board 79 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 53 79 105 landing || decide (bonus 53 p ≤ 1 - Generated.soko3_2Potential.boulder 79 - Generated.soko3_2Potential.hole landing + bonus 79 (change p 79 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check73 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check74 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir53_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 .east p = true := by
  change ((!walkGuard soko3_2.board support p 53 54 .east || decide (bonus 53 p ≤ bonus 54 p)) && ((PreciseRolling.stayTargets soko3_2.board 54 .east).all (fun landing => !pushGuard support p 53 54 55 landing || decide (bonus 53 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some landing)))) && (pushTargets soko3_2.board 54 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 53 54 55 landing || decide (bonus 53 p ≤ 1 - Generated.soko3_2Potential.boulder 54 - Generated.soko3_2Potential.hole landing + bonus 54 (change p 54 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check75 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check76 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir53_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 .west p = true := by
  rfl
theorem dir53_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 53 28 .northEast || decide (bonus 53 p ≤ bonus 28 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check77 p, rfl⟩
theorem dir53_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 .northWest p = true := by
  rfl
theorem dir53_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 53 80 .southEast || decide (bonus 53 p ≤ bonus 80 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check78 p, rfl⟩
theorem dir53_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 53 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
