import NetHack.Sokoban12CostPartition.Directions03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir76_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 .north p = true := by
  change ((!walkGuard soko1_2.board support p 76 50 .north || decide (bonus 76 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check155 p, rfl⟩
theorem dir76_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 .south p = true := by
  change ((!walkGuard soko1_2.board support p 76 102 .south || decide (bonus 76 p ≤ bonus 102 p)) && ((PreciseRolling.stayTargets soko1_2.board 102 .south).all (fun landing => !pushGuard support p 76 102 128 landing || decide (bonus 76 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 102 + bonus 102 (change p 102 (some landing)))) && (pushTargets soko1_2.board 102 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 76 102 128 landing || decide (bonus 76 p ≤ 1 - Generated.soko1_2Potential.boulder 102 - Generated.soko1_2Potential.hole landing + bonus 102 (change p 102 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check156 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check157 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir76_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 .east p = true := by
  rfl
theorem dir76_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 .west p = true := by
  rfl
theorem dir76_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 .northEast p = true := by
  rfl
theorem dir76_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 76 49 .northWest || decide (bonus 76 p ≤ bonus 49 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check158 p, rfl⟩
theorem dir76_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 .southEast p = true := by
  rfl
theorem dir76_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 76 .southWest p = true := by
  rfl
theorem dir82_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 .north p = true := by
  change ((!walkGuard soko1_2.board support p 82 56 .north || decide (bonus 82 p ≤ bonus 56 p)) && ((PreciseRolling.stayTargets soko1_2.board 56 .north).all (fun landing => !pushGuard support p 82 56 30 landing || decide (bonus 82 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 56 + bonus 56 (change p 56 (some landing)))) && (pushTargets soko1_2.board 56 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 82 56 30 landing || decide (bonus 82 p ≤ 1 - Generated.soko1_2Potential.boulder 56 - Generated.soko1_2Potential.hole landing + bonus 56 (change p 56 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check159 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check160 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir82_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 .south p = true := by
  change ((!walkGuard soko1_2.board support p 82 108 .south || decide (bonus 82 p ≤ bonus 108 p)) && ((PreciseRolling.stayTargets soko1_2.board 108 .south).all (fun landing => !pushGuard support p 82 108 134 landing || decide (bonus 82 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 108 + bonus 108 (change p 108 (some landing)))) && (pushTargets soko1_2.board 108 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 82 108 134 landing || decide (bonus 82 p ≤ 1 - Generated.soko1_2Potential.boulder 108 - Generated.soko1_2Potential.hole landing + bonus 108 (change p 108 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check161 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check162 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir82_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 .east p = true := by
  rfl
theorem dir82_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 .west p = true := by
  rfl
theorem dir82_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 .northEast p = true := by
  rfl
theorem dir82_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 82 55 .northWest || decide (bonus 82 p ≤ bonus 55 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check163 p, rfl⟩
theorem dir82_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 .southEast p = true := by
  rfl
theorem dir82_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 82 .southWest p = true := by
  rfl
theorem dir102_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 .north p = true := by
  change ((!walkGuard soko1_2.board support p 102 76 .north || decide (bonus 102 p ≤ bonus 76 p)) && ((PreciseRolling.stayTargets soko1_2.board 76 .north).all (fun landing => !pushGuard support p 102 76 50 landing || decide (bonus 102 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 76 + bonus 76 (change p 76 (some landing)))) && (pushTargets soko1_2.board 76 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 102 76 50 landing || decide (bonus 102 p ≤ 1 - Generated.soko1_2Potential.boulder 76 - Generated.soko1_2Potential.hole landing + bonus 76 (change p 76 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check164 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check165 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir102_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 .south p = true := by
  change ((!walkGuard soko1_2.board support p 102 128 .south || decide (bonus 102 p ≤ bonus 128 p)) && ((PreciseRolling.stayTargets soko1_2.board 128 .south).all (fun landing => !pushGuard support p 102 128 154 landing || decide (bonus 102 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 128 + bonus 128 (change p 128 (some landing)))) && (pushTargets soko1_2.board 128 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 102 128 154 landing || decide (bonus 102 p ≤ 1 - Generated.soko1_2Potential.boulder 128 - Generated.soko1_2Potential.hole landing + bonus 128 (change p 128 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check166 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check167 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir102_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 .east p = true := by
  rfl
theorem dir102_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 .west p = true := by
  rfl
theorem dir102_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 .northEast p = true := by
  rfl
theorem dir102_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 .northWest p = true := by
  rfl
theorem dir102_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 .southEast p = true := by
  rfl
theorem dir102_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 102 .southWest p = true := by
  rfl
theorem dir105_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 .north p = true := by
  rfl
theorem dir105_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 .south p = true := by
  change ((!walkGuard soko1_2.board support p 105 131 .south || decide (bonus 105 p ≤ bonus 131 p)) && ((PreciseRolling.stayTargets soko1_2.board 131 .south).all (fun landing => !pushGuard support p 105 131 157 landing || decide (bonus 105 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 131 + bonus 131 (change p 131 (some landing)))) && (pushTargets soko1_2.board 131 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 105 131 157 landing || decide (bonus 105 p ≤ 1 - Generated.soko1_2Potential.boulder 131 - Generated.soko1_2Potential.hole landing + bonus 131 (change p 131 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check168 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check169 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir105_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 .east p = true := by
  change ((!walkGuard soko1_2.board support p 105 106 .east || decide (bonus 105 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check170 p, rfl⟩
theorem dir105_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 .west p = true := by
  rfl
theorem dir105_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 .northEast p = true := by
  rfl
theorem dir105_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 .northWest p = true := by
  rfl
theorem dir105_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 105 132 .southEast || decide (bonus 105 p ≤ bonus 132 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check171 p, rfl⟩
theorem dir105_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 105 .southWest p = true := by
  rfl
theorem dir106_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 .north p = true := by
  rfl
theorem dir106_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 .south p = true := by
  change ((!walkGuard soko1_2.board support p 106 132 .south || decide (bonus 106 p ≤ bonus 132 p)) && ((PreciseRolling.stayTargets soko1_2.board 132 .south).all (fun landing => !pushGuard support p 106 132 158 landing || decide (bonus 106 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some landing)))) && (pushTargets soko1_2.board 132 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 106 132 158 landing || decide (bonus 106 p ≤ 1 - Generated.soko1_2Potential.boulder 132 - Generated.soko1_2Potential.hole landing + bonus 132 (change p 132 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check172 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check173 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir106_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 .east p = true := by
  rfl
theorem dir106_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 .west p = true := by
  change ((!walkGuard soko1_2.board support p 106 105 .west || decide (bonus 106 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check174 p, rfl⟩
theorem dir106_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 .northEast p = true := by
  rfl
theorem dir106_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 .northWest p = true := by
  rfl
theorem dir106_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 106 133 .southEast || decide (bonus 106 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check175 p, rfl⟩
theorem dir106_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 106 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 106 131 .southWest || decide (bonus 106 p ≤ bonus 131 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check176 p, rfl⟩
theorem dir108_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 .north p = true := by
  change ((!walkGuard soko1_2.board support p 108 82 .north || decide (bonus 108 p ≤ bonus 82 p)) && ((PreciseRolling.stayTargets soko1_2.board 82 .north).all (fun landing => !pushGuard support p 108 82 56 landing || decide (bonus 108 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 82 + bonus 82 (change p 82 (some landing)))) && (pushTargets soko1_2.board 82 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 108 82 56 landing || decide (bonus 108 p ≤ 1 - Generated.soko1_2Potential.boulder 82 - Generated.soko1_2Potential.hole landing + bonus 82 (change p 82 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check177 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check178 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir108_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 .south p = true := by
  change ((!walkGuard soko1_2.board support p 108 134 .south || decide (bonus 108 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko1_2.board 134 .south).all (fun landing => !pushGuard support p 108 134 160 landing || decide (bonus 108 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko1_2.board 134 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 108 134 160 landing || decide (bonus 108 p ≤ 1 - Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check179 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check180 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir108_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 .east p = true := by
  rfl
theorem dir108_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 .west p = true := by
  rfl
theorem dir108_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 .northEast p = true := by
  rfl
theorem dir108_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 .northWest p = true := by
  rfl
theorem dir108_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 108 135 .southEast || decide (bonus 108 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check181 p, rfl⟩
theorem dir108_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 108 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 108 133 .southWest || decide (bonus 108 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check182 p, rfl⟩
end NetHack.Sokoban12CostPartition
