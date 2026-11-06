import NetHack.Sokoban12CostPartition.Directions00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir35_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 .north p = true := by
  rfl
theorem dir35_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 .south p = true := by
  rfl
theorem dir35_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 .east p = true := by
  change ((!walkGuard soko1_2.board support p 35 36 .east || decide (bonus 35 p ≤ bonus 36 p)) && ((PreciseRolling.stayTargets soko1_2.board 36 .east).all (fun landing => !pushGuard support p 35 36 37 landing || decide (bonus 35 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 36 + bonus 36 (change p 36 (some landing)))) && (pushTargets soko1_2.board 36 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 35 36 37 landing || decide (bonus 35 p ≤ 1 - Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.hole landing + bonus 36 (change p 36 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check52 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check53 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check54 p, (by intro cell member; cases member)⟩)
theorem dir35_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 .west p = true := by
  change ((!walkGuard soko1_2.board support p 35 34 .west || decide (bonus 35 p ≤ bonus 34 p)) && ((PreciseRolling.stayTargets soko1_2.board 34 .west).all (fun landing => !pushGuard support p 35 34 33 landing || decide (bonus 35 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 34 + bonus 34 (change p 34 (some landing)))) && (pushTargets soko1_2.board 34 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 35 34 33 landing || decide (bonus 35 p ≤ 1 - Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.hole landing + bonus 34 (change p 34 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check55 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check56 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check57 p, (by intro cell member; cases member)⟩)
theorem dir35_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 .northEast p = true := by
  rfl
theorem dir35_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 .northWest p = true := by
  rfl
theorem dir35_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 .southEast p = true := by
  rfl
theorem dir35_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 35 .southWest p = true := by
  rfl
theorem dir36_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 .north p = true := by
  rfl
theorem dir36_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 .south p = true := by
  rfl
theorem dir36_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 .east p = true := by
  change ((!walkGuard soko1_2.board support p 36 37 .east || decide (bonus 36 p ≤ bonus 37 p)) && ((PreciseRolling.stayTargets soko1_2.board 37 .east).all (fun landing => !pushGuard support p 36 37 38 landing || decide (bonus 36 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 37 + bonus 37 (change p 37 (some landing)))) && (pushTargets soko1_2.board 37 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 36 37 38 landing || decide (bonus 36 p ≤ 1 - Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.hole landing + bonus 37 (change p 37 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check58 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check59 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check60 p, (by intro cell member; cases member)⟩)
theorem dir36_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 .west p = true := by
  change ((!walkGuard soko1_2.board support p 36 35 .west || decide (bonus 36 p ≤ bonus 35 p)) && ((PreciseRolling.stayTargets soko1_2.board 35 .west).all (fun landing => !pushGuard support p 36 35 34 landing || decide (bonus 36 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 35 + bonus 35 (change p 35 (some landing)))) && (pushTargets soko1_2.board 35 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 36 35 34 landing || decide (bonus 36 p ≤ 1 - Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.hole landing + bonus 35 (change p 35 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check61 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check62 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check63 p, (by intro cell member; cases member)⟩)
theorem dir36_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 .northEast p = true := by
  rfl
theorem dir36_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 .northWest p = true := by
  rfl
theorem dir36_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 .southEast p = true := by
  rfl
theorem dir36_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 36 .southWest p = true := by
  rfl
theorem dir37_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 .north p = true := by
  rfl
theorem dir37_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 .south p = true := by
  rfl
theorem dir37_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 .east p = true := by
  change ((!walkGuard soko1_2.board support p 37 38 .east || decide (bonus 37 p ≤ bonus 38 p)) && ((PreciseRolling.stayTargets soko1_2.board 38 .east).all (fun landing => !pushGuard support p 37 38 39 landing || decide (bonus 37 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 38 + bonus 38 (change p 38 (some landing)))) && (pushTargets soko1_2.board 38 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 37 38 39 landing || decide (bonus 37 p ≤ 1 - Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.hole landing + bonus 38 (change p 38 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check64 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check65 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check66 p, (by intro cell member; cases member)⟩)
theorem dir37_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 .west p = true := by
  change ((!walkGuard soko1_2.board support p 37 36 .west || decide (bonus 37 p ≤ bonus 36 p)) && ((PreciseRolling.stayTargets soko1_2.board 36 .west).all (fun landing => !pushGuard support p 37 36 35 landing || decide (bonus 37 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 36 + bonus 36 (change p 36 (some landing)))) && (pushTargets soko1_2.board 36 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 37 36 35 landing || decide (bonus 37 p ≤ 1 - Generated.soko1_2Potential.boulder 36 - Generated.soko1_2Potential.hole landing + bonus 36 (change p 36 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check67 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check68 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check69 p, (by intro cell member; cases member)⟩)
theorem dir37_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 .northEast p = true := by
  rfl
theorem dir37_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 .northWest p = true := by
  rfl
theorem dir37_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 .southEast p = true := by
  rfl
theorem dir37_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 37 .southWest p = true := by
  rfl
theorem dir38_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 .north p = true := by
  rfl
theorem dir38_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 .south p = true := by
  rfl
theorem dir38_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 .east p = true := by
  change ((!walkGuard soko1_2.board support p 38 39 .east || decide (bonus 38 p ≤ bonus 39 p)) && ((PreciseRolling.stayTargets soko1_2.board 39 .east).all (fun landing => !pushGuard support p 38 39 40 landing || decide (bonus 38 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 39 + bonus 39 (change p 39 (some landing)))) && (pushTargets soko1_2.board 39 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 38 39 40 landing || decide (bonus 38 p ≤ 1 - Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.hole landing + bonus 39 (change p 39 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check70 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check71 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check72 p, (by intro cell member; cases member)⟩)
theorem dir38_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 .west p = true := by
  change ((!walkGuard soko1_2.board support p 38 37 .west || decide (bonus 38 p ≤ bonus 37 p)) && ((PreciseRolling.stayTargets soko1_2.board 37 .west).all (fun landing => !pushGuard support p 38 37 36 landing || decide (bonus 38 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 37 + bonus 37 (change p 37 (some landing)))) && (pushTargets soko1_2.board 37 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 38 37 36 landing || decide (bonus 38 p ≤ 1 - Generated.soko1_2Potential.boulder 37 - Generated.soko1_2Potential.hole landing + bonus 37 (change p 37 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check73 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check74 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check75 p, (by intro cell member; cases member)⟩)
theorem dir38_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 .northEast p = true := by
  rfl
theorem dir38_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 .northWest p = true := by
  rfl
theorem dir38_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 .southEast p = true := by
  rfl
theorem dir38_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 38 .southWest p = true := by
  rfl
theorem dir39_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 .north p = true := by
  rfl
theorem dir39_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 .south p = true := by
  rfl
theorem dir39_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 .east p = true := by
  change ((!walkGuard soko1_2.board support p 39 40 .east || decide (bonus 39 p ≤ bonus 40 p)) && ((PreciseRolling.stayTargets soko1_2.board 40 .east).all (fun landing => !pushGuard support p 39 40 41 landing || decide (bonus 39 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 40 + bonus 40 (change p 40 (some landing)))) && (pushTargets soko1_2.board 40 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 39 40 41 landing || decide (bonus 39 p ≤ 1 - Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.hole landing + bonus 40 (change p 40 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check76 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check77 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check78 p, (by intro cell member; cases member)⟩)
theorem dir39_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 .west p = true := by
  change ((!walkGuard soko1_2.board support p 39 38 .west || decide (bonus 39 p ≤ bonus 38 p)) && ((PreciseRolling.stayTargets soko1_2.board 38 .west).all (fun landing => !pushGuard support p 39 38 37 landing || decide (bonus 39 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 38 + bonus 38 (change p 38 (some landing)))) && (pushTargets soko1_2.board 38 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 39 38 37 landing || decide (bonus 39 p ≤ 1 - Generated.soko1_2Potential.boulder 38 - Generated.soko1_2Potential.hole landing + bonus 38 (change p 38 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check79 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check80 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check81 p, (by intro cell member; cases member)⟩)
theorem dir39_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 .northEast p = true := by
  rfl
theorem dir39_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 .northWest p = true := by
  rfl
theorem dir39_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 .southEast p = true := by
  rfl
theorem dir39_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 39 .southWest p = true := by
  rfl
theorem dir40_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 .north p = true := by
  rfl
theorem dir40_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 .south p = true := by
  rfl
theorem dir40_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 .east p = true := by
  change ((!walkGuard soko1_2.board support p 40 41 .east || decide (bonus 40 p ≤ bonus 41 p)) && ((PreciseRolling.stayTargets soko1_2.board 41 .east).all (fun landing => !pushGuard support p 40 41 42 landing || decide (bonus 40 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 41 + bonus 41 (change p 41 (some landing)))) && (pushTargets soko1_2.board 41 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 40 41 42 landing || decide (bonus 40 p ≤ 1 - Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.hole landing + bonus 41 (change p 41 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check82 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check83 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check84 p, (by intro cell member; cases member)⟩)
theorem dir40_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 .west p = true := by
  change ((!walkGuard soko1_2.board support p 40 39 .west || decide (bonus 40 p ≤ bonus 39 p)) && ((PreciseRolling.stayTargets soko1_2.board 39 .west).all (fun landing => !pushGuard support p 40 39 38 landing || decide (bonus 40 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 39 + bonus 39 (change p 39 (some landing)))) && (pushTargets soko1_2.board 39 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 40 39 38 landing || decide (bonus 40 p ≤ 1 - Generated.soko1_2Potential.boulder 39 - Generated.soko1_2Potential.hole landing + bonus 39 (change p 39 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check85 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check86 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check87 p, (by intro cell member; cases member)⟩)
theorem dir40_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 .northEast p = true := by
  rfl
theorem dir40_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 .northWest p = true := by
  rfl
theorem dir40_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 .southEast p = true := by
  rfl
theorem dir40_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 40 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
