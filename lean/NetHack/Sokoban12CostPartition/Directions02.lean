import NetHack.Sokoban12CostPartition.Directions01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir41_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 .north p = true := by
  rfl
theorem dir41_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 .south p = true := by
  rfl
theorem dir41_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 .east p = true := by
  change ((!walkGuard soko1_2.board support p 41 42 .east || decide (bonus 41 p ≤ bonus 42 p)) && ((PreciseRolling.stayTargets soko1_2.board 42 .east).all (fun landing => !pushGuard support p 41 42 43 landing || decide (bonus 41 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 42 + bonus 42 (change p 42 (some landing)))) && (pushTargets soko1_2.board 42 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 41 42 43 landing || decide (bonus 41 p ≤ 1 - Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.hole landing + bonus 42 (change p 42 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check88 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check89 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check90 p, (by intro cell member; cases member)⟩)
theorem dir41_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 .west p = true := by
  change ((!walkGuard soko1_2.board support p 41 40 .west || decide (bonus 41 p ≤ bonus 40 p)) && ((PreciseRolling.stayTargets soko1_2.board 40 .west).all (fun landing => !pushGuard support p 41 40 39 landing || decide (bonus 41 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 40 + bonus 40 (change p 40 (some landing)))) && (pushTargets soko1_2.board 40 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 41 40 39 landing || decide (bonus 41 p ≤ 1 - Generated.soko1_2Potential.boulder 40 - Generated.soko1_2Potential.hole landing + bonus 40 (change p 40 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check91 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check92 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check93 p, (by intro cell member; cases member)⟩)
theorem dir41_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 .northEast p = true := by
  rfl
theorem dir41_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 .northWest p = true := by
  rfl
theorem dir41_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 .southEast p = true := by
  rfl
theorem dir41_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 41 .southWest p = true := by
  rfl
theorem dir42_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 .north p = true := by
  rfl
theorem dir42_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 .south p = true := by
  rfl
theorem dir42_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 .east p = true := by
  change ((!walkGuard soko1_2.board support p 42 43 .east || decide (bonus 42 p ≤ bonus 43 p)) && ((PreciseRolling.stayTargets soko1_2.board 43 .east).all (fun landing => !pushGuard support p 42 43 44 landing || decide (bonus 42 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 43 + bonus 43 (change p 43 (some landing)))) && (pushTargets soko1_2.board 43 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 42 43 44 landing || decide (bonus 42 p ≤ 1 - Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.hole landing + bonus 43 (change p 43 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check94 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check95 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check96 p, (by intro cell member; cases member)⟩)
theorem dir42_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 .west p = true := by
  change ((!walkGuard soko1_2.board support p 42 41 .west || decide (bonus 42 p ≤ bonus 41 p)) && ((PreciseRolling.stayTargets soko1_2.board 41 .west).all (fun landing => !pushGuard support p 42 41 40 landing || decide (bonus 42 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 41 + bonus 41 (change p 41 (some landing)))) && (pushTargets soko1_2.board 41 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 42 41 40 landing || decide (bonus 42 p ≤ 1 - Generated.soko1_2Potential.boulder 41 - Generated.soko1_2Potential.hole landing + bonus 41 (change p 41 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check97 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check98 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check99 p, (by intro cell member; cases member)⟩)
theorem dir42_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 .northEast p = true := by
  rfl
theorem dir42_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 .northWest p = true := by
  rfl
theorem dir42_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 .southEast p = true := by
  rfl
theorem dir42_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 42 .southWest p = true := by
  rfl
theorem dir43_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 .north p = true := by
  rfl
theorem dir43_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 .south p = true := by
  rfl
theorem dir43_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 .east p = true := by
  change ((!walkGuard soko1_2.board support p 43 44 .east || decide (bonus 43 p ≤ bonus 44 p)) && ((PreciseRolling.stayTargets soko1_2.board 44 .east).all (fun landing => !pushGuard support p 43 44 45 landing || decide (bonus 43 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 44 + bonus 44 (change p 44 (some landing)))) && (pushTargets soko1_2.board 44 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 43 44 45 landing || decide (bonus 43 p ≤ 1 - Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.hole landing + bonus 44 (change p 44 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check100 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check101 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check102 p, (by intro cell member; cases member)⟩)
theorem dir43_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 .west p = true := by
  change ((!walkGuard soko1_2.board support p 43 42 .west || decide (bonus 43 p ≤ bonus 42 p)) && ((PreciseRolling.stayTargets soko1_2.board 42 .west).all (fun landing => !pushGuard support p 43 42 41 landing || decide (bonus 43 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 42 + bonus 42 (change p 42 (some landing)))) && (pushTargets soko1_2.board 42 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 43 42 41 landing || decide (bonus 43 p ≤ 1 - Generated.soko1_2Potential.boulder 42 - Generated.soko1_2Potential.hole landing + bonus 42 (change p 42 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check103 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check104 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check105 p, (by intro cell member; cases member)⟩)
theorem dir43_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 .northEast p = true := by
  rfl
theorem dir43_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 .northWest p = true := by
  rfl
theorem dir43_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 .southEast p = true := by
  rfl
theorem dir43_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 43 .southWest p = true := by
  rfl
theorem dir44_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 .north p = true := by
  rfl
theorem dir44_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 .south p = true := by
  rfl
theorem dir44_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 .east p = true := by
  change ((!walkGuard soko1_2.board support p 44 45 .east || decide (bonus 44 p ≤ bonus 45 p)) && ((PreciseRolling.stayTargets soko1_2.board 45 .east).all (fun landing => !pushGuard support p 44 45 46 landing || decide (bonus 44 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 45 + bonus 45 (change p 45 (some landing)))) && (pushTargets soko1_2.board 45 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 44 45 46 landing || decide (bonus 44 p ≤ 1 - Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.hole landing + bonus 45 (change p 45 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check106 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check107 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check108 p, (by intro cell member; cases member)⟩)
theorem dir44_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 .west p = true := by
  change ((!walkGuard soko1_2.board support p 44 43 .west || decide (bonus 44 p ≤ bonus 43 p)) && ((PreciseRolling.stayTargets soko1_2.board 43 .west).all (fun landing => !pushGuard support p 44 43 42 landing || decide (bonus 44 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 43 + bonus 43 (change p 43 (some landing)))) && (pushTargets soko1_2.board 43 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 44 43 42 landing || decide (bonus 44 p ≤ 1 - Generated.soko1_2Potential.boulder 43 - Generated.soko1_2Potential.hole landing + bonus 43 (change p 43 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check109 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check110 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check111 p, (by intro cell member; cases member)⟩)
theorem dir44_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 .northEast p = true := by
  rfl
theorem dir44_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 .northWest p = true := by
  rfl
theorem dir44_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 .southEast p = true := by
  rfl
theorem dir44_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 44 .southWest p = true := by
  rfl
theorem dir45_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 .north p = true := by
  rfl
theorem dir45_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 .south p = true := by
  rfl
theorem dir45_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 .east p = true := by
  change ((!walkGuard soko1_2.board support p 45 46 .east || decide (bonus 45 p ≤ bonus 46 p)) && ((PreciseRolling.stayTargets soko1_2.board 46 .east).all (fun landing => !pushGuard support p 45 46 47 landing || decide (bonus 45 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 46 + bonus 46 (change p 46 (some landing)))) && (pushTargets soko1_2.board 46 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 45 46 47 landing || decide (bonus 45 p ≤ 1 - Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.hole landing + bonus 46 (change p 46 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check112 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check113 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check114 p, (by intro cell member; cases member)⟩)
theorem dir45_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 .west p = true := by
  change ((!walkGuard soko1_2.board support p 45 44 .west || decide (bonus 45 p ≤ bonus 44 p)) && ((PreciseRolling.stayTargets soko1_2.board 44 .west).all (fun landing => !pushGuard support p 45 44 43 landing || decide (bonus 45 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 44 + bonus 44 (change p 44 (some landing)))) && (pushTargets soko1_2.board 44 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 45 44 43 landing || decide (bonus 45 p ≤ 1 - Generated.soko1_2Potential.boulder 44 - Generated.soko1_2Potential.hole landing + bonus 44 (change p 44 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check115 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check116 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check117 p, (by intro cell member; cases member)⟩)
theorem dir45_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 .northEast p = true := by
  rfl
theorem dir45_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 .northWest p = true := by
  rfl
theorem dir45_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 .southEast p = true := by
  rfl
theorem dir45_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 45 .southWest p = true := by
  rfl
theorem dir46_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 .north p = true := by
  rfl
theorem dir46_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 .south p = true := by
  rfl
theorem dir46_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 .east p = true := by
  change ((!walkGuard soko1_2.board support p 46 47 .east || decide (bonus 46 p ≤ bonus 47 p)) && ((PreciseRolling.stayTargets soko1_2.board 47 .east).all (fun landing => !pushGuard support p 46 47 48 landing || decide (bonus 46 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 47 + bonus 47 (change p 47 (some landing)))) && (pushTargets soko1_2.board 47 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 46 47 48 landing || decide (bonus 46 p ≤ 1 - Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.hole landing + bonus 47 (change p 47 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check118 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check119 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check120 p, (by intro cell member; cases member)⟩)
theorem dir46_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 .west p = true := by
  change ((!walkGuard soko1_2.board support p 46 45 .west || decide (bonus 46 p ≤ bonus 45 p)) && ((PreciseRolling.stayTargets soko1_2.board 45 .west).all (fun landing => !pushGuard support p 46 45 44 landing || decide (bonus 46 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 45 + bonus 45 (change p 45 (some landing)))) && (pushTargets soko1_2.board 45 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 46 45 44 landing || decide (bonus 46 p ≤ 1 - Generated.soko1_2Potential.boulder 45 - Generated.soko1_2Potential.hole landing + bonus 45 (change p 45 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check121 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check122 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check123 p, (by intro cell member; cases member)⟩)
theorem dir46_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 .northEast p = true := by
  rfl
theorem dir46_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 .northWest p = true := by
  rfl
theorem dir46_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 .southEast p = true := by
  rfl
theorem dir46_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 46 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
