import NetHack.Sokoban22Refined85.Directions11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir156_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 .north p = true := by
  change ((!walkGuard soko2_2.board support p 156 134 .north || decide (bonus 156 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check582 p, rfl⟩
theorem dir156_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 .south p = true := by
  rfl
theorem dir156_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 .east p = true := by
  change ((!walkGuard soko2_2.board support p 156 157 .east || decide (bonus 156 p ≤ bonus 157 p)) && ((PreciseRolling.stayTargets soko2_2.board 157 .east).all (fun landing => !pushGuard support p 156 157 158 landing || decide (bonus 156 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 157 + bonus 157 (change p 157 (some landing)))) && (pushTargets soko2_2.board 157 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 156 157 158 landing || decide (bonus 156 p ≤ 1 - Generated.soko2_2Potential.boulder 157 - Generated.soko2_2Potential.hole landing + bonus 157 (change p 157 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check583 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check584 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir156_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 .west p = true := by
  change ((!walkGuard soko2_2.board support p 156 155 .west || decide (bonus 156 p ≤ bonus 155 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check585 p, rfl⟩
theorem dir156_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 156 135 .northEast || decide (bonus 156 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check586 p, rfl⟩
theorem dir156_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 156 133 .northWest || decide (bonus 156 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check587 p, rfl⟩
theorem dir156_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 .southEast p = true := by
  rfl
theorem dir156_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 156 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 156 177 .southWest || decide (bonus 156 p ≤ bonus 177 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check588 p, rfl⟩
theorem dir157_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 .north p = true := by
  change ((!walkGuard soko2_2.board support p 157 135 .north || decide (bonus 157 p ≤ bonus 135 p)) && ((PreciseRolling.stayTargets soko2_2.board 135 .north).all (fun landing => !pushGuard support p 157 135 113 landing || decide (bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some landing)))) && (pushTargets soko2_2.board 135 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 157 135 113 landing || decide (bonus 157 p ≤ 1 - Generated.soko2_2Potential.boulder 135 - Generated.soko2_2Potential.hole landing + bonus 135 (change p 135 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check589 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check590 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir157_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 .south p = true := by
  rfl
theorem dir157_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 .east p = true := by
  change ((!walkGuard soko2_2.board support p 157 158 .east || decide (bonus 157 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko2_2.board 158 .east).all (fun landing => !pushGuard support p 157 158 159 landing || decide (bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko2_2.board 158 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 157 158 159 landing || decide (bonus 157 p ≤ 1 - Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check591 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check592 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir157_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 .west p = true := by
  change ((!walkGuard soko2_2.board support p 157 156 .west || decide (bonus 157 p ≤ bonus 156 p)) && ((PreciseRolling.stayTargets soko2_2.board 156 .west).all (fun landing => !pushGuard support p 157 156 155 landing || decide (bonus 157 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 156 + bonus 156 (change p 156 (some landing)))) && (pushTargets soko2_2.board 156 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 157 156 155 landing || decide (bonus 157 p ≤ 1 - Generated.soko2_2Potential.boulder 156 - Generated.soko2_2Potential.hole landing + bonus 156 (change p 156 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check593 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check594 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir157_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 157 136 .northEast || decide (bonus 157 p ≤ bonus 136 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check595 p, rfl⟩
theorem dir157_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 157 134 .northWest || decide (bonus 157 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check596 p, rfl⟩
theorem dir157_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 157 180 .southEast || decide (bonus 157 p ≤ bonus 180 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check597 p, rfl⟩
theorem dir157_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 157 .southWest p = true := by
  rfl
theorem dir158_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 .north p = true := by
  change ((!walkGuard soko2_2.board support p 158 136 .north || decide (bonus 158 p ≤ bonus 136 p)) && ((PreciseRolling.stayTargets soko2_2.board 136 .north).all (fun landing => !pushGuard support p 158 136 114 landing || decide (bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 136 + bonus 136 (change p 136 (some landing)))) && (pushTargets soko2_2.board 136 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 158 136 114 landing || decide (bonus 158 p ≤ 1 - Generated.soko2_2Potential.boulder 136 - Generated.soko2_2Potential.hole landing + bonus 136 (change p 136 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check598 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check599 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 .south p = true := by
  change ((!walkGuard soko2_2.board support p 158 180 .south || decide (bonus 158 p ≤ bonus 180 p)) && ((PreciseRolling.stayTargets soko2_2.board 180 .south).all (fun landing => !pushGuard support p 158 180 202 landing || decide (bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 180 + bonus 180 (change p 180 (some landing)))) && (pushTargets soko2_2.board 180 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 158 180 202 landing || decide (bonus 158 p ≤ 1 - Generated.soko2_2Potential.boulder 180 - Generated.soko2_2Potential.hole landing + bonus 180 (change p 180 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check600 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check601 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 .east p = true := by
  change ((!walkGuard soko2_2.board support p 158 159 .east || decide (bonus 158 p ≤ bonus 159 p)) && ((PreciseRolling.stayTargets soko2_2.board 159 .east).all (fun landing => !pushGuard support p 158 159 160 landing || decide (bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 159 + bonus 159 (change p 159 (some landing)))) && (pushTargets soko2_2.board 159 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 158 159 160 landing || decide (bonus 158 p ≤ 1 - Generated.soko2_2Potential.boulder 159 - Generated.soko2_2Potential.hole landing + bonus 159 (change p 159 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check602 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check603 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 .west p = true := by
  change ((!walkGuard soko2_2.board support p 158 157 .west || decide (bonus 158 p ≤ bonus 157 p)) && ((PreciseRolling.stayTargets soko2_2.board 157 .west).all (fun landing => !pushGuard support p 158 157 156 landing || decide (bonus 158 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 157 + bonus 157 (change p 157 (some landing)))) && (pushTargets soko2_2.board 157 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 158 157 156 landing || decide (bonus 158 p ≤ 1 - Generated.soko2_2Potential.boulder 157 - Generated.soko2_2Potential.hole landing + bonus 157 (change p 157 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check604 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check605 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 .northEast p = true := by
  rfl
theorem dir158_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 158 135 .northWest || decide (bonus 158 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check606 p, rfl⟩
theorem dir158_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 158 181 .southEast || decide (bonus 158 p ≤ bonus 181 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check607 p, rfl⟩
theorem dir158_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 158 .southWest p = true := by
  rfl
theorem dir159_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 .north p = true := by
  rfl
theorem dir159_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 .south p = true := by
  change ((!walkGuard soko2_2.board support p 159 181 .south || decide (bonus 159 p ≤ bonus 181 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check608 p, rfl⟩
theorem dir159_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 .east p = true := by
  change ((!walkGuard soko2_2.board support p 159 160 .east || decide (bonus 159 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko2_2.board 160 .east).all (fun landing => !pushGuard support p 159 160 161 landing || decide (bonus 159 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko2_2.board 160 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 159 160 161 landing || decide (bonus 159 p ≤ 1 - Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check609 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check610 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir159_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 .west p = true := by
  change ((!walkGuard soko2_2.board support p 159 158 .west || decide (bonus 159 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko2_2.board 158 .west).all (fun landing => !pushGuard support p 159 158 157 landing || decide (bonus 159 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko2_2.board 158 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 159 158 157 landing || decide (bonus 159 p ≤ 1 - Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check611 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check612 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir159_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 159 138 .northEast || decide (bonus 159 p ≤ bonus 138 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check613 p, rfl⟩
theorem dir159_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 159 136 .northWest || decide (bonus 159 p ≤ bonus 136 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check614 p, rfl⟩
theorem dir159_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 159 182 .southEast || decide (bonus 159 p ≤ bonus 182 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check615 p, rfl⟩
theorem dir159_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 159 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 159 180 .southWest || decide (bonus 159 p ≤ bonus 180 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check616 p, rfl⟩
theorem dir160_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 .north p = true := by
  change ((!walkGuard soko2_2.board support p 160 138 .north || decide (bonus 160 p ≤ bonus 138 p)) && ((PreciseRolling.stayTargets soko2_2.board 138 .north).all (fun landing => !pushGuard support p 160 138 116 landing || decide (bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 138 + bonus 138 (change p 138 (some landing)))) && (pushTargets soko2_2.board 138 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 160 138 116 landing || decide (bonus 160 p ≤ 1 - Generated.soko2_2Potential.boulder 138 - Generated.soko2_2Potential.hole landing + bonus 138 (change p 138 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check617 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check618 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 .south p = true := by
  change ((!walkGuard soko2_2.board support p 160 182 .south || decide (bonus 160 p ≤ bonus 182 p)) && ((PreciseRolling.stayTargets soko2_2.board 182 .south).all (fun landing => !pushGuard support p 160 182 204 landing || decide (bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 182 + bonus 182 (change p 182 (some landing)))) && (pushTargets soko2_2.board 182 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 160 182 204 landing || decide (bonus 160 p ≤ 1 - Generated.soko2_2Potential.boulder 182 - Generated.soko2_2Potential.hole landing + bonus 182 (change p 182 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check619 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check620 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 .east p = true := by
  change ((!walkGuard soko2_2.board support p 160 161 .east || decide (bonus 160 p ≤ bonus 161 p)) && ((PreciseRolling.stayTargets soko2_2.board 161 .east).all (fun landing => !pushGuard support p 160 161 162 landing || decide (bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 161 + bonus 161 (change p 161 (some landing)))) && (pushTargets soko2_2.board 161 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 160 161 162 landing || decide (bonus 160 p ≤ 1 - Generated.soko2_2Potential.boulder 161 - Generated.soko2_2Potential.hole landing + bonus 161 (change p 161 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check621 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check622 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 .west p = true := by
  change ((!walkGuard soko2_2.board support p 160 159 .west || decide (bonus 160 p ≤ bonus 159 p)) && ((PreciseRolling.stayTargets soko2_2.board 159 .west).all (fun landing => !pushGuard support p 160 159 158 landing || decide (bonus 160 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 159 + bonus 159 (change p 159 (some landing)))) && (pushTargets soko2_2.board 159 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 160 159 158 landing || decide (bonus 160 p ≤ 1 - Generated.soko2_2Potential.boulder 159 - Generated.soko2_2Potential.hole landing + bonus 159 (change p 159 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check623 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check624 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 .northEast p = true := by
  rfl
theorem dir160_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 .northWest p = true := by
  rfl
theorem dir160_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 .southEast p = true := by
  rfl
theorem dir160_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 160 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 160 181 .southWest || decide (bonus 160 p ≤ bonus 181 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check625 p, rfl⟩
theorem dir161_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 .north p = true := by
  rfl
theorem dir161_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 .south p = true := by
  rfl
theorem dir161_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 .east p = true := by
  change ((!walkGuard soko2_2.board support p 161 162 .east || decide (bonus 161 p ≤ bonus 162 p)) && ((PreciseRolling.stayTargets soko2_2.board 162 .east).all (fun landing => !pushGuard support p 161 162 163 landing || decide (bonus 161 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 162 + bonus 162 (change p 162 (some landing)))) && (pushTargets soko2_2.board 162 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 161 162 163 landing || decide (bonus 161 p ≤ 1 - Generated.soko2_2Potential.boulder 162 - Generated.soko2_2Potential.hole landing + bonus 162 (change p 162 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check626 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check627 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir161_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 .west p = true := by
  change ((!walkGuard soko2_2.board support p 161 160 .west || decide (bonus 161 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko2_2.board 160 .west).all (fun landing => !pushGuard support p 161 160 159 landing || decide (bonus 161 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko2_2.board 160 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 161 160 159 landing || decide (bonus 161 p ≤ 1 - Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check628 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check629 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir161_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 .northEast p = true := by
  rfl
theorem dir161_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 161 138 .northWest || decide (bonus 161 p ≤ bonus 138 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check630 p, rfl⟩
theorem dir161_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 161 184 .southEast || decide (bonus 161 p ≤ bonus 184 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check631 p, rfl⟩
theorem dir161_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 161 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 161 182 .southWest || decide (bonus 161 p ≤ bonus 182 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check632 p, rfl⟩
end NetHack.Sokoban22Refined85
