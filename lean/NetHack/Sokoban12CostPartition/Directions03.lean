import NetHack.Sokoban12CostPartition.Directions02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir47_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 .north p = true := by
  rfl
theorem dir47_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 .south p = true := by
  rfl
theorem dir47_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 .east p = true := by
  change ((!walkGuard soko1_2.board support p 47 48 .east || decide (bonus 47 p ≤ bonus 48 p)) && ((PreciseRolling.stayTargets soko1_2.board 48 .east).all (fun landing => !pushGuard support p 47 48 49 landing || decide (bonus 47 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 48 + bonus 48 (change p 48 (some landing)))) && (pushTargets soko1_2.board 48 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 47 48 49 landing || decide (bonus 47 p ≤ 1 - Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.hole landing + bonus 48 (change p 48 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check124 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check125 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check126 p, (by intro cell member; cases member)⟩)
theorem dir47_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 .west p = true := by
  change ((!walkGuard soko1_2.board support p 47 46 .west || decide (bonus 47 p ≤ bonus 46 p)) && ((PreciseRolling.stayTargets soko1_2.board 46 .west).all (fun landing => !pushGuard support p 47 46 45 landing || decide (bonus 47 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 46 + bonus 46 (change p 46 (some landing)))) && (pushTargets soko1_2.board 46 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 47 46 45 landing || decide (bonus 47 p ≤ 1 - Generated.soko1_2Potential.boulder 46 - Generated.soko1_2Potential.hole landing + bonus 46 (change p 46 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check127 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check128 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check129 p, (by intro cell member; cases member)⟩)
theorem dir47_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 .northEast p = true := by
  rfl
theorem dir47_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 .northWest p = true := by
  rfl
theorem dir47_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 .southEast p = true := by
  rfl
theorem dir47_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 47 .southWest p = true := by
  rfl
theorem dir48_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 .north p = true := by
  rfl
theorem dir48_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 .south p = true := by
  rfl
theorem dir48_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 .east p = true := by
  change ((!walkGuard soko1_2.board support p 48 49 .east || decide (bonus 48 p ≤ bonus 49 p)) && ((PreciseRolling.stayTargets soko1_2.board 49 .east).all (fun landing => !pushGuard support p 48 49 50 landing || decide (bonus 48 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 49 + bonus 49 (change p 49 (some landing)))) && (pushTargets soko1_2.board 49 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 48 49 50 landing || decide (bonus 48 p ≤ 1 - Generated.soko1_2Potential.boulder 49 - Generated.soko1_2Potential.hole landing + bonus 49 (change p 49 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check130 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check131 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir48_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 .west p = true := by
  change ((!walkGuard soko1_2.board support p 48 47 .west || decide (bonus 48 p ≤ bonus 47 p)) && ((PreciseRolling.stayTargets soko1_2.board 47 .west).all (fun landing => !pushGuard support p 48 47 46 landing || decide (bonus 48 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 47 + bonus 47 (change p 47 (some landing)))) && (pushTargets soko1_2.board 47 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 48 47 46 landing || decide (bonus 48 p ≤ 1 - Generated.soko1_2Potential.boulder 47 - Generated.soko1_2Potential.hole landing + bonus 47 (change p 47 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check132 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check133 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check134 p, (by intro cell member; cases member)⟩)
theorem dir48_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 .northEast p = true := by
  rfl
theorem dir48_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 .northWest p = true := by
  rfl
theorem dir48_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 .southEast p = true := by
  rfl
theorem dir48_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 48 .southWest p = true := by
  rfl
theorem dir49_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 .north p = true := by
  rfl
theorem dir49_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 .south p = true := by
  rfl
theorem dir49_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 .east p = true := by
  change ((!walkGuard soko1_2.board support p 49 50 .east || decide (bonus 49 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check135 p, rfl⟩
theorem dir49_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 .west p = true := by
  change ((!walkGuard soko1_2.board support p 49 48 .west || decide (bonus 49 p ≤ bonus 48 p)) && ((PreciseRolling.stayTargets soko1_2.board 48 .west).all (fun landing => !pushGuard support p 49 48 47 landing || decide (bonus 49 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 48 + bonus 48 (change p 48 (some landing)))) && (pushTargets soko1_2.board 48 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 49 48 47 landing || decide (bonus 49 p ≤ 1 - Generated.soko1_2Potential.boulder 48 - Generated.soko1_2Potential.hole landing + bonus 48 (change p 48 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check136 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check137 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check138 p, (by intro cell member; cases member)⟩)
theorem dir49_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 .northEast p = true := by
  rfl
theorem dir49_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 .northWest p = true := by
  rfl
theorem dir49_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 49 76 .southEast || decide (bonus 49 p ≤ bonus 76 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check139 p, rfl⟩
theorem dir49_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 49 .southWest p = true := by
  rfl
theorem dir50_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 .north p = true := by
  rfl
theorem dir50_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 .south p = true := by
  change ((!walkGuard soko1_2.board support p 50 76 .south || decide (bonus 50 p ≤ bonus 76 p)) && ((PreciseRolling.stayTargets soko1_2.board 76 .south).all (fun landing => !pushGuard support p 50 76 102 landing || decide (bonus 50 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 76 + bonus 76 (change p 76 (some landing)))) && (pushTargets soko1_2.board 76 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 50 76 102 landing || decide (bonus 50 p ≤ 1 - Generated.soko1_2Potential.boulder 76 - Generated.soko1_2Potential.hole landing + bonus 76 (change p 76 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check140 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check141 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir50_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 .east p = true := by
  rfl
theorem dir50_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 .west p = true := by
  change ((!walkGuard soko1_2.board support p 50 49 .west || decide (bonus 50 p ≤ bonus 49 p)) && ((PreciseRolling.stayTargets soko1_2.board 49 .west).all (fun landing => !pushGuard support p 50 49 48 landing || decide (bonus 50 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 49 + bonus 49 (change p 49 (some landing)))) && (pushTargets soko1_2.board 49 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 50 49 48 landing || decide (bonus 50 p ≤ 1 - Generated.soko1_2Potential.boulder 49 - Generated.soko1_2Potential.hole landing + bonus 49 (change p 49 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check142 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check143 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check144 p, (by intro cell member; cases member)⟩)
theorem dir50_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 .northEast p = true := by
  rfl
theorem dir50_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 .northWest p = true := by
  rfl
theorem dir50_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 .southEast p = true := by
  rfl
theorem dir50_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 50 .southWest p = true := by
  rfl
theorem dir55_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 .north p = true := by
  change ((!walkGuard soko1_2.board support p 55 29 .north || decide (bonus 55 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check145 p, rfl⟩
theorem dir55_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 .south p = true := by
  rfl
theorem dir55_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 .east p = true := by
  change ((!walkGuard soko1_2.board support p 55 56 .east || decide (bonus 55 p ≤ bonus 56 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check146 p, rfl⟩
theorem dir55_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 .west p = true := by
  rfl
theorem dir55_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 55 30 .northEast || decide (bonus 55 p ≤ bonus 30 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check147 p, rfl⟩
theorem dir55_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 .northWest p = true := by
  rfl
theorem dir55_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 55 82 .southEast || decide (bonus 55 p ≤ bonus 82 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check148 p, rfl⟩
theorem dir55_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 55 .southWest p = true := by
  rfl
theorem dir56_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 .north p = true := by
  change ((!walkGuard soko1_2.board support p 56 30 .north || decide (bonus 56 p ≤ bonus 30 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check149 p, rfl⟩
theorem dir56_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 .south p = true := by
  change ((!walkGuard soko1_2.board support p 56 82 .south || decide (bonus 56 p ≤ bonus 82 p)) && ((PreciseRolling.stayTargets soko1_2.board 82 .south).all (fun landing => !pushGuard support p 56 82 108 landing || decide (bonus 56 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 82 + bonus 82 (change p 82 (some landing)))) && (pushTargets soko1_2.board 82 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 56 82 108 landing || decide (bonus 56 p ≤ 1 - Generated.soko1_2Potential.boulder 82 - Generated.soko1_2Potential.hole landing + bonus 82 (change p 82 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check150 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check151 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir56_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 .east p = true := by
  rfl
theorem dir56_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 .west p = true := by
  change ((!walkGuard soko1_2.board support p 56 55 .west || decide (bonus 56 p ≤ bonus 55 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check152 p, rfl⟩
theorem dir56_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 56 31 .northEast || decide (bonus 56 p ≤ bonus 31 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check153 p, rfl⟩
theorem dir56_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 56 29 .northWest || decide (bonus 56 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check154 p, rfl⟩
theorem dir56_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 .southEast p = true := by
  rfl
theorem dir56_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 56 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
