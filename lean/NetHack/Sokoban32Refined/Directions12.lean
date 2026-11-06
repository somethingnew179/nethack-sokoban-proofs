import NetHack.Sokoban32Refined.Directions11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir149_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 .north p = true := by
  change ((!walkGuard soko3_2.board support p 149 123 .north || decide (bonus 149 p ≤ bonus 123 p)) && ((PreciseRolling.stayTargets soko3_2.board 123 .north).all (fun landing => !pushGuard support p 149 123 97 landing || decide (bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 123 + bonus 123 (change p 123 (some landing)))) && (pushTargets soko3_2.board 123 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 149 123 97 landing || decide (bonus 149 p ≤ 1 - Generated.soko3_2Potential.boulder 123 - Generated.soko3_2Potential.hole landing + bonus 123 (change p 123 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check598 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check599 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir149_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 .south p = true := by
  change ((!walkGuard soko3_2.board support p 149 175 .south || decide (bonus 149 p ≤ bonus 175 p)) && ((PreciseRolling.stayTargets soko3_2.board 175 .south).all (fun landing => !pushGuard support p 149 175 201 landing || decide (bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some landing)))) && (pushTargets soko3_2.board 175 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 149 175 201 landing || decide (bonus 149 p ≤ 1 - Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.hole landing + bonus 175 (change p 175 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check600 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check601 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir149_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 .east p = true := by
  change ((!walkGuard soko3_2.board support p 149 150 .east || decide (bonus 149 p ≤ bonus 150 p)) && ((PreciseRolling.stayTargets soko3_2.board 150 .east).all (fun landing => !pushGuard support p 149 150 151 landing || decide (bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some landing)))) && (pushTargets soko3_2.board 150 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 149 150 151 landing || decide (bonus 149 p ≤ 1 - Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.hole landing + bonus 150 (change p 150 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check602 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check603 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir149_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 .west p = true := by
  change ((!walkGuard soko3_2.board support p 149 148 .west || decide (bonus 149 p ≤ bonus 148 p)) && ((PreciseRolling.stayTargets soko3_2.board 148 .west).all (fun landing => !pushGuard support p 149 148 147 landing || decide (bonus 149 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some landing)))) && (pushTargets soko3_2.board 148 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 149 148 147 landing || decide (bonus 149 p ≤ 1 - Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.hole landing + bonus 148 (change p 148 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check604 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check605 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir149_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 149 124 .northEast || decide (bonus 149 p ≤ bonus 124 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check606 p, rfl⟩
theorem dir149_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 149 122 .northWest || decide (bonus 149 p ≤ bonus 122 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check607 p, rfl⟩
theorem dir149_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 149 176 .southEast || decide (bonus 149 p ≤ bonus 176 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check608 p, rfl⟩
theorem dir149_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 149 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 149 174 .southWest || decide (bonus 149 p ≤ bonus 174 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check609 p, rfl⟩
theorem dir150_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 .north p = true := by
  change ((!walkGuard soko3_2.board support p 150 124 .north || decide (bonus 150 p ≤ bonus 124 p)) && ((PreciseRolling.stayTargets soko3_2.board 124 .north).all (fun landing => !pushGuard support p 150 124 98 landing || decide (bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 124 + bonus 124 (change p 124 (some landing)))) && (pushTargets soko3_2.board 124 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 150 124 98 landing || decide (bonus 150 p ≤ 1 - Generated.soko3_2Potential.boulder 124 - Generated.soko3_2Potential.hole landing + bonus 124 (change p 124 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check610 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check611 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir150_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 .south p = true := by
  change ((!walkGuard soko3_2.board support p 150 176 .south || decide (bonus 150 p ≤ bonus 176 p)) && ((PreciseRolling.stayTargets soko3_2.board 176 .south).all (fun landing => !pushGuard support p 150 176 202 landing || decide (bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some landing)))) && (pushTargets soko3_2.board 176 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 150 176 202 landing || decide (bonus 150 p ≤ 1 - Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.hole landing + bonus 176 (change p 176 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check612 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check613 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir150_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 .east p = true := by
  change ((!walkGuard soko3_2.board support p 150 151 .east || decide (bonus 150 p ≤ bonus 151 p)) && ((PreciseRolling.stayTargets soko3_2.board 151 .east).all (fun landing => !pushGuard support p 150 151 152 landing || decide (bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some landing)))) && (pushTargets soko3_2.board 151 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 150 151 152 landing || decide (bonus 150 p ≤ 1 - Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.hole landing + bonus 151 (change p 151 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check614 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check615 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir150_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 .west p = true := by
  change ((!walkGuard soko3_2.board support p 150 149 .west || decide (bonus 150 p ≤ bonus 149 p)) && ((PreciseRolling.stayTargets soko3_2.board 149 .west).all (fun landing => !pushGuard support p 150 149 148 landing || decide (bonus 150 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some landing)))) && (pushTargets soko3_2.board 149 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 150 149 148 landing || decide (bonus 150 p ≤ 1 - Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.hole landing + bonus 149 (change p 149 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check616 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check617 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir150_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 150 125 .northEast || decide (bonus 150 p ≤ bonus 125 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check618 p, rfl⟩
theorem dir150_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 150 123 .northWest || decide (bonus 150 p ≤ bonus 123 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check619 p, rfl⟩
theorem dir150_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 150 177 .southEast || decide (bonus 150 p ≤ bonus 177 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check620 p, rfl⟩
theorem dir150_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 150 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 150 175 .southWest || decide (bonus 150 p ≤ bonus 175 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check621 p, rfl⟩
theorem dir151_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 .north p = true := by
  change ((!walkGuard soko3_2.board support p 151 125 .north || decide (bonus 151 p ≤ bonus 125 p)) && ((PreciseRolling.stayTargets soko3_2.board 125 .north).all (fun landing => !pushGuard support p 151 125 99 landing || decide (bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 125 + bonus 125 (change p 125 (some landing)))) && (pushTargets soko3_2.board 125 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 151 125 99 landing || decide (bonus 151 p ≤ 1 - Generated.soko3_2Potential.boulder 125 - Generated.soko3_2Potential.hole landing + bonus 125 (change p 125 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check622 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check623 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir151_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 .south p = true := by
  change ((!walkGuard soko3_2.board support p 151 177 .south || decide (bonus 151 p ≤ bonus 177 p)) && ((PreciseRolling.stayTargets soko3_2.board 177 .south).all (fun landing => !pushGuard support p 151 177 203 landing || decide (bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some landing)))) && (pushTargets soko3_2.board 177 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 151 177 203 landing || decide (bonus 151 p ≤ 1 - Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.hole landing + bonus 177 (change p 177 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check624 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check625 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir151_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 .east p = true := by
  change ((!walkGuard soko3_2.board support p 151 152 .east || decide (bonus 151 p ≤ bonus 152 p)) && ((PreciseRolling.stayTargets soko3_2.board 152 .east).all (fun landing => !pushGuard support p 151 152 153 landing || decide (bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some landing)))) && (pushTargets soko3_2.board 152 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 151 152 153 landing || decide (bonus 151 p ≤ 1 - Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.hole landing + bonus 152 (change p 152 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check626 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check627 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir151_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 .west p = true := by
  change ((!walkGuard soko3_2.board support p 151 150 .west || decide (bonus 151 p ≤ bonus 150 p)) && ((PreciseRolling.stayTargets soko3_2.board 150 .west).all (fun landing => !pushGuard support p 151 150 149 landing || decide (bonus 151 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some landing)))) && (pushTargets soko3_2.board 150 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 151 150 149 landing || decide (bonus 151 p ≤ 1 - Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.hole landing + bonus 150 (change p 150 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check628 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check629 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir151_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 151 126 .northEast || decide (bonus 151 p ≤ bonus 126 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check630 p, rfl⟩
theorem dir151_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 151 124 .northWest || decide (bonus 151 p ≤ bonus 124 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check631 p, rfl⟩
theorem dir151_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 151 178 .southEast || decide (bonus 151 p ≤ bonus 178 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check632 p, rfl⟩
theorem dir151_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 151 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 151 176 .southWest || decide (bonus 151 p ≤ bonus 176 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check633 p, rfl⟩
theorem dir152_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 .north p = true := by
  change ((!walkGuard soko3_2.board support p 152 126 .north || decide (bonus 152 p ≤ bonus 126 p)) && ((PreciseRolling.stayTargets soko3_2.board 126 .north).all (fun landing => !pushGuard support p 152 126 100 landing || decide (bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 126 + bonus 126 (change p 126 (some landing)))) && (pushTargets soko3_2.board 126 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 152 126 100 landing || decide (bonus 152 p ≤ 1 - Generated.soko3_2Potential.boulder 126 - Generated.soko3_2Potential.hole landing + bonus 126 (change p 126 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check634 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check635 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir152_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 .south p = true := by
  change ((!walkGuard soko3_2.board support p 152 178 .south || decide (bonus 152 p ≤ bonus 178 p)) && ((PreciseRolling.stayTargets soko3_2.board 178 .south).all (fun landing => !pushGuard support p 152 178 204 landing || decide (bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some landing)))) && (pushTargets soko3_2.board 178 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 152 178 204 landing || decide (bonus 152 p ≤ 1 - Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.hole landing + bonus 178 (change p 178 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check636 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check637 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir152_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 .east p = true := by
  change ((!walkGuard soko3_2.board support p 152 153 .east || decide (bonus 152 p ≤ bonus 153 p)) && ((PreciseRolling.stayTargets soko3_2.board 153 .east).all (fun landing => !pushGuard support p 152 153 154 landing || decide (bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some landing)))) && (pushTargets soko3_2.board 153 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 152 153 154 landing || decide (bonus 152 p ≤ 1 - Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.hole landing + bonus 153 (change p 153 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check638 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check639 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir152_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 .west p = true := by
  change ((!walkGuard soko3_2.board support p 152 151 .west || decide (bonus 152 p ≤ bonus 151 p)) && ((PreciseRolling.stayTargets soko3_2.board 151 .west).all (fun landing => !pushGuard support p 152 151 150 landing || decide (bonus 152 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some landing)))) && (pushTargets soko3_2.board 151 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 152 151 150 landing || decide (bonus 152 p ≤ 1 - Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.hole landing + bonus 151 (change p 151 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check640 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check641 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir152_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 152 127 .northEast || decide (bonus 152 p ≤ bonus 127 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check642 p, rfl⟩
theorem dir152_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 152 125 .northWest || decide (bonus 152 p ≤ bonus 125 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check643 p, rfl⟩
theorem dir152_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 152 179 .southEast || decide (bonus 152 p ≤ bonus 179 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check644 p, rfl⟩
theorem dir152_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 152 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 152 177 .southWest || decide (bonus 152 p ≤ bonus 177 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check645 p, rfl⟩
theorem dir153_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 .north p = true := by
  change ((!walkGuard soko3_2.board support p 153 127 .north || decide (bonus 153 p ≤ bonus 127 p)) && ((PreciseRolling.stayTargets soko3_2.board 127 .north).all (fun landing => !pushGuard support p 153 127 101 landing || decide (bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 127 + bonus 127 (change p 127 (some landing)))) && (pushTargets soko3_2.board 127 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 153 127 101 landing || decide (bonus 153 p ≤ 1 - Generated.soko3_2Potential.boulder 127 - Generated.soko3_2Potential.hole landing + bonus 127 (change p 127 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check646 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check647 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir153_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 .south p = true := by
  change ((!walkGuard soko3_2.board support p 153 179 .south || decide (bonus 153 p ≤ bonus 179 p)) && ((PreciseRolling.stayTargets soko3_2.board 179 .south).all (fun landing => !pushGuard support p 153 179 205 landing || decide (bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some landing)))) && (pushTargets soko3_2.board 179 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 153 179 205 landing || decide (bonus 153 p ≤ 1 - Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.hole landing + bonus 179 (change p 179 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check648 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check649 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir153_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 .east p = true := by
  change ((!walkGuard soko3_2.board support p 153 154 .east || decide (bonus 153 p ≤ bonus 154 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check650 p, rfl⟩
theorem dir153_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 .west p = true := by
  change ((!walkGuard soko3_2.board support p 153 152 .west || decide (bonus 153 p ≤ bonus 152 p)) && ((PreciseRolling.stayTargets soko3_2.board 152 .west).all (fun landing => !pushGuard support p 153 152 151 landing || decide (bonus 153 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some landing)))) && (pushTargets soko3_2.board 152 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 153 152 151 landing || decide (bonus 153 p ≤ 1 - Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.hole landing + bonus 152 (change p 152 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check651 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check652 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir153_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 153 128 .northEast || decide (bonus 153 p ≤ bonus 128 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check653 p, rfl⟩
theorem dir153_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 153 126 .northWest || decide (bonus 153 p ≤ bonus 126 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check654 p, rfl⟩
theorem dir153_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 153 180 .southEast || decide (bonus 153 p ≤ bonus 180 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check655 p, rfl⟩
theorem dir153_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 153 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 153 178 .southWest || decide (bonus 153 p ≤ bonus 178 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check656 p, rfl⟩
theorem dir154_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 .north p = true := by
  change ((!walkGuard soko3_2.board support p 154 128 .north || decide (bonus 154 p ≤ bonus 128 p)) && ((PreciseRolling.stayTargets soko3_2.board 128 .north).all (fun landing => !pushGuard support p 154 128 102 landing || decide (bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 128 + bonus 128 (change p 128 (some landing)))) && (pushTargets soko3_2.board 128 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 154 128 102 landing || decide (bonus 154 p ≤ 1 - Generated.soko3_2Potential.boulder 128 - Generated.soko3_2Potential.hole landing + bonus 128 (change p 128 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check657 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check658 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir154_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 .south p = true := by
  change ((!walkGuard soko3_2.board support p 154 180 .south || decide (bonus 154 p ≤ bonus 180 p)) && ((PreciseRolling.stayTargets soko3_2.board 180 .south).all (fun landing => !pushGuard support p 154 180 206 landing || decide (bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 180 + bonus 180 (change p 180 (some landing)))) && (pushTargets soko3_2.board 180 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 154 180 206 landing || decide (bonus 154 p ≤ 1 - Generated.soko3_2Potential.boulder 180 - Generated.soko3_2Potential.hole landing + bonus 180 (change p 180 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check659 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check660 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir154_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 .east p = true := by
  rfl
theorem dir154_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 .west p = true := by
  change ((!walkGuard soko3_2.board support p 154 153 .west || decide (bonus 154 p ≤ bonus 153 p)) && ((PreciseRolling.stayTargets soko3_2.board 153 .west).all (fun landing => !pushGuard support p 154 153 152 landing || decide (bonus 154 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some landing)))) && (pushTargets soko3_2.board 153 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 154 153 152 landing || decide (bonus 154 p ≤ 1 - Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.hole landing + bonus 153 (change p 153 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check661 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check662 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir154_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 .northEast p = true := by
  rfl
theorem dir154_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 154 127 .northWest || decide (bonus 154 p ≤ bonus 127 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check663 p, rfl⟩
theorem dir154_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 .southEast p = true := by
  rfl
theorem dir154_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 154 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 154 179 .southWest || decide (bonus 154 p ≤ bonus 179 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check664 p, rfl⟩
end NetHack.Sokoban32Refined
