import NetHack.Sokoban32Refined.Directions10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir137_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 .north p = true := by
  rfl
theorem dir137_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 .south p = true := by
  change ((!walkGuard soko3_2.board support p 137 163 .south || decide (bonus 137 p ≤ bonus 163 p)) && ((PreciseRolling.stayTargets soko3_2.board 163 .south).all (fun landing => !pushGuard support p 137 163 189 landing || decide (bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 163 + bonus 163 (change p 163 (some landing)))) && (pushTargets soko3_2.board 163 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 137 163 189 landing || decide (bonus 137 p ≤ 1 - Generated.soko3_2Potential.boulder 163 - Generated.soko3_2Potential.hole landing + bonus 163 (change p 163 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check543 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check544 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir137_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 .east p = true := by
  change ((!walkGuard soko3_2.board support p 137 138 .east || decide (bonus 137 p ≤ bonus 138 p)) && ((PreciseRolling.stayTargets soko3_2.board 138 .east).all (fun landing => !pushGuard support p 137 138 139 landing || decide (bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 138 + bonus 138 (change p 138 (some landing)))) && (pushTargets soko3_2.board 138 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 137 138 139 landing || decide (bonus 137 p ≤ 1 - Generated.soko3_2Potential.boulder 138 - Generated.soko3_2Potential.hole landing + bonus 138 (change p 138 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check545 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check546 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir137_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 .west p = true := by
  change ((!walkGuard soko3_2.board support p 137 136 .west || decide (bonus 137 p ≤ bonus 136 p)) && ((PreciseRolling.stayTargets soko3_2.board 136 .west).all (fun landing => !pushGuard support p 137 136 135 landing || decide (bonus 137 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some landing)))) && (pushTargets soko3_2.board 136 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 137 136 135 landing || decide (bonus 137 p ≤ 1 - Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.hole landing + bonus 136 (change p 136 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check547 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check548 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir137_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 137 112 .northEast || decide (bonus 137 p ≤ bonus 112 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check549 p, rfl⟩
theorem dir137_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 137 110 .northWest || decide (bonus 137 p ≤ bonus 110 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check550 p, rfl⟩
theorem dir137_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 .southEast p = true := by
  rfl
theorem dir137_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 137 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 137 162 .southWest || decide (bonus 137 p ≤ bonus 162 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check551 p, rfl⟩
theorem dir138_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 .north p = true := by
  change ((!walkGuard soko3_2.board support p 138 112 .north || decide (bonus 138 p ≤ bonus 112 p)) && ((PreciseRolling.stayTargets soko3_2.board 112 .north).all (fun landing => !pushGuard support p 138 112 86 landing || decide (bonus 138 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 112 + bonus 112 (change p 112 (some landing)))) && (pushTargets soko3_2.board 112 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 138 112 86 landing || decide (bonus 138 p ≤ 1 - Generated.soko3_2Potential.boulder 112 - Generated.soko3_2Potential.hole landing + bonus 112 (change p 112 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check552 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check553 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir138_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 .south p = true := by
  rfl
theorem dir138_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 .east p = true := by
  change ((!walkGuard soko3_2.board support p 138 139 .east || decide (bonus 138 p ≤ bonus 139 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check554 p, rfl⟩
theorem dir138_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 .west p = true := by
  change ((!walkGuard soko3_2.board support p 138 137 .west || decide (bonus 138 p ≤ bonus 137 p)) && ((PreciseRolling.stayTargets soko3_2.board 137 .west).all (fun landing => !pushGuard support p 138 137 136 landing || decide (bonus 138 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 137 + bonus 137 (change p 137 (some landing)))) && (pushTargets soko3_2.board 137 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 138 137 136 landing || decide (bonus 138 p ≤ 1 - Generated.soko3_2Potential.boulder 137 - Generated.soko3_2Potential.hole landing + bonus 137 (change p 137 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check555 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check556 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir138_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 138 113 .northEast || decide (bonus 138 p ≤ bonus 113 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check557 p, rfl⟩
theorem dir138_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 .northWest p = true := by
  rfl
theorem dir138_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 138 165 .southEast || decide (bonus 138 p ≤ bonus 165 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check558 p, rfl⟩
theorem dir138_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 138 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 138 163 .southWest || decide (bonus 138 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check559 p, rfl⟩
theorem dir139_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 .north p = true := by
  change ((!walkGuard soko3_2.board support p 139 113 .north || decide (bonus 139 p ≤ bonus 113 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check560 p, rfl⟩
theorem dir139_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 .south p = true := by
  change ((!walkGuard soko3_2.board support p 139 165 .south || decide (bonus 139 p ≤ bonus 165 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check561 p, rfl⟩
theorem dir139_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 .east p = true := by
  rfl
theorem dir139_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 .west p = true := by
  change ((!walkGuard soko3_2.board support p 139 138 .west || decide (bonus 139 p ≤ bonus 138 p)) && ((PreciseRolling.stayTargets soko3_2.board 138 .west).all (fun landing => !pushGuard support p 139 138 137 landing || decide (bonus 139 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 138 + bonus 138 (change p 138 (some landing)))) && (pushTargets soko3_2.board 138 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 139 138 137 landing || decide (bonus 139 p ≤ 1 - Generated.soko3_2Potential.boulder 138 - Generated.soko3_2Potential.hole landing + bonus 138 (change p 138 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check562 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check563 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir139_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 139 114 .northEast || decide (bonus 139 p ≤ bonus 114 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check564 p, rfl⟩
theorem dir139_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 139 112 .northWest || decide (bonus 139 p ≤ bonus 112 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check565 p, rfl⟩
theorem dir139_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 139 166 .southEast || decide (bonus 139 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check566 p, rfl⟩
theorem dir139_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 139 .southWest p = true := by
  rfl
theorem dir146_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 .north p = true := by
  change ((!walkGuard soko3_2.board support p 146 120 .north || decide (bonus 146 p ≤ bonus 120 p)) && ((PreciseRolling.stayTargets soko3_2.board 120 .north).all (fun landing => !pushGuard support p 146 120 94 landing || decide (bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 120 + bonus 120 (change p 120 (some landing)))) && (pushTargets soko3_2.board 120 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 146 120 94 landing || decide (bonus 146 p ≤ 1 - Generated.soko3_2Potential.boulder 120 - Generated.soko3_2Potential.hole landing + bonus 120 (change p 120 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check567 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check568 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir146_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 .south p = true := by
  change ((!walkGuard soko3_2.board support p 146 172 .south || decide (bonus 146 p ≤ bonus 172 p)) && ((PreciseRolling.stayTargets soko3_2.board 172 .south).all (fun landing => !pushGuard support p 146 172 198 landing || decide (bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 172 + bonus 172 (change p 172 (some landing)))) && (pushTargets soko3_2.board 172 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 146 172 198 landing || decide (bonus 146 p ≤ 1 - Generated.soko3_2Potential.boulder 172 - Generated.soko3_2Potential.hole landing + bonus 172 (change p 172 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check569 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check570 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir146_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 .east p = true := by
  change ((!walkGuard soko3_2.board support p 146 147 .east || decide (bonus 146 p ≤ bonus 147 p)) && ((PreciseRolling.stayTargets soko3_2.board 147 .east).all (fun landing => !pushGuard support p 146 147 148 landing || decide (bonus 146 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some landing)))) && (pushTargets soko3_2.board 147 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 146 147 148 landing || decide (bonus 146 p ≤ 1 - Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.hole landing + bonus 147 (change p 147 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check571 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check572 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir146_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 .west p = true := by
  rfl
theorem dir146_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 146 121 .northEast || decide (bonus 146 p ≤ bonus 121 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check573 p, rfl⟩
theorem dir146_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 .northWest p = true := by
  rfl
theorem dir146_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 146 173 .southEast || decide (bonus 146 p ≤ bonus 173 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check574 p, rfl⟩
theorem dir146_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 146 .southWest p = true := by
  rfl
theorem dir147_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 .north p = true := by
  change ((!walkGuard soko3_2.board support p 147 121 .north || decide (bonus 147 p ≤ bonus 121 p)) && ((PreciseRolling.stayTargets soko3_2.board 121 .north).all (fun landing => !pushGuard support p 147 121 95 landing || decide (bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 121 + bonus 121 (change p 121 (some landing)))) && (pushTargets soko3_2.board 121 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 147 121 95 landing || decide (bonus 147 p ≤ 1 - Generated.soko3_2Potential.boulder 121 - Generated.soko3_2Potential.hole landing + bonus 121 (change p 121 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check575 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check576 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir147_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 .south p = true := by
  change ((!walkGuard soko3_2.board support p 147 173 .south || decide (bonus 147 p ≤ bonus 173 p)) && ((PreciseRolling.stayTargets soko3_2.board 173 .south).all (fun landing => !pushGuard support p 147 173 199 landing || decide (bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some landing)))) && (pushTargets soko3_2.board 173 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 147 173 199 landing || decide (bonus 147 p ≤ 1 - Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.hole landing + bonus 173 (change p 173 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check577 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check578 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir147_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 .east p = true := by
  change ((!walkGuard soko3_2.board support p 147 148 .east || decide (bonus 147 p ≤ bonus 148 p)) && ((PreciseRolling.stayTargets soko3_2.board 148 .east).all (fun landing => !pushGuard support p 147 148 149 landing || decide (bonus 147 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some landing)))) && (pushTargets soko3_2.board 148 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 147 148 149 landing || decide (bonus 147 p ≤ 1 - Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.hole landing + bonus 148 (change p 148 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check579 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check580 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir147_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 .west p = true := by
  change ((!walkGuard soko3_2.board support p 147 146 .west || decide (bonus 147 p ≤ bonus 146 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check581 p, rfl⟩
theorem dir147_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 147 122 .northEast || decide (bonus 147 p ≤ bonus 122 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check582 p, rfl⟩
theorem dir147_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 147 120 .northWest || decide (bonus 147 p ≤ bonus 120 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check583 p, rfl⟩
theorem dir147_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 147 174 .southEast || decide (bonus 147 p ≤ bonus 174 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check584 p, rfl⟩
theorem dir147_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 147 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 147 172 .southWest || decide (bonus 147 p ≤ bonus 172 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check585 p, rfl⟩
theorem dir148_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 .north p = true := by
  change ((!walkGuard soko3_2.board support p 148 122 .north || decide (bonus 148 p ≤ bonus 122 p)) && ((PreciseRolling.stayTargets soko3_2.board 122 .north).all (fun landing => !pushGuard support p 148 122 96 landing || decide (bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 122 + bonus 122 (change p 122 (some landing)))) && (pushTargets soko3_2.board 122 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 148 122 96 landing || decide (bonus 148 p ≤ 1 - Generated.soko3_2Potential.boulder 122 - Generated.soko3_2Potential.hole landing + bonus 122 (change p 122 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check586 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check587 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir148_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 .south p = true := by
  change ((!walkGuard soko3_2.board support p 148 174 .south || decide (bonus 148 p ≤ bonus 174 p)) && ((PreciseRolling.stayTargets soko3_2.board 174 .south).all (fun landing => !pushGuard support p 148 174 200 landing || decide (bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some landing)))) && (pushTargets soko3_2.board 174 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 148 174 200 landing || decide (bonus 148 p ≤ 1 - Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.hole landing + bonus 174 (change p 174 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check588 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check589 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir148_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 .east p = true := by
  change ((!walkGuard soko3_2.board support p 148 149 .east || decide (bonus 148 p ≤ bonus 149 p)) && ((PreciseRolling.stayTargets soko3_2.board 149 .east).all (fun landing => !pushGuard support p 148 149 150 landing || decide (bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some landing)))) && (pushTargets soko3_2.board 149 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 148 149 150 landing || decide (bonus 148 p ≤ 1 - Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.hole landing + bonus 149 (change p 149 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check590 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check591 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir148_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 .west p = true := by
  change ((!walkGuard soko3_2.board support p 148 147 .west || decide (bonus 148 p ≤ bonus 147 p)) && ((PreciseRolling.stayTargets soko3_2.board 147 .west).all (fun landing => !pushGuard support p 148 147 146 landing || decide (bonus 148 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some landing)))) && (pushTargets soko3_2.board 147 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 148 147 146 landing || decide (bonus 148 p ≤ 1 - Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.hole landing + bonus 147 (change p 147 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check592 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check593 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir148_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 148 123 .northEast || decide (bonus 148 p ≤ bonus 123 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check594 p, rfl⟩
theorem dir148_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 148 121 .northWest || decide (bonus 148 p ≤ bonus 121 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check595 p, rfl⟩
theorem dir148_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 148 175 .southEast || decide (bonus 148 p ≤ bonus 175 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check596 p, rfl⟩
theorem dir148_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 148 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 148 173 .southWest || decide (bonus 148 p ≤ bonus 173 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check597 p, rfl⟩
end NetHack.Sokoban32Refined
