import NetHack.Sokoban22Refined85.Directions10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir146_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 .north p = true := by
  change ((!walkGuard soko2_2.board support p 146 124 .north || decide (bonus 146 p ≤ bonus 124 p)) && ((PreciseRolling.stayTargets soko2_2.board 124 .north).all (fun landing => !pushGuard support p 146 124 102 landing || decide (bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 124 + bonus 124 (change p 124 (some landing)))) && (pushTargets soko2_2.board 124 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 146 124 102 landing || decide (bonus 146 p ≤ 1 - Generated.soko2_2Potential.boulder 124 - Generated.soko2_2Potential.hole landing + bonus 124 (change p 124 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check520 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check521 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir146_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 .south p = true := by
  change ((!walkGuard soko2_2.board support p 146 168 .south || decide (bonus 146 p ≤ bonus 168 p)) && ((PreciseRolling.stayTargets soko2_2.board 168 .south).all (fun landing => !pushGuard support p 146 168 190 landing || decide (bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some landing)))) && (pushTargets soko2_2.board 168 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 146 168 190 landing || decide (bonus 146 p ≤ 1 - Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.hole landing + bonus 168 (change p 168 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check522 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check523 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir146_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 .east p = true := by
  change ((!walkGuard soko2_2.board support p 146 147 .east || decide (bonus 146 p ≤ bonus 147 p)) && ((PreciseRolling.stayTargets soko2_2.board 147 .east).all (fun landing => !pushGuard support p 146 147 148 landing || decide (bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some landing)))) && (pushTargets soko2_2.board 147 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 146 147 148 landing || decide (bonus 146 p ≤ 1 - Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.hole landing + bonus 147 (change p 147 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check524 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check525 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir146_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 .west p = true := by
  change ((!walkGuard soko2_2.board support p 146 145 .west || decide (bonus 146 p ≤ bonus 145 p)) && ((PreciseRolling.stayTargets soko2_2.board 145 .west).all (fun landing => !pushGuard support p 146 145 144 landing || decide (bonus 146 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some landing)))) && (pushTargets soko2_2.board 145 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 146 145 144 landing || decide (bonus 146 p ≤ 1 - Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.hole landing + bonus 145 (change p 145 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check526 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check527 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir146_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 146 125 .northEast || decide (bonus 146 p ≤ bonus 125 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check528 p, rfl⟩
theorem dir146_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 146 123 .northWest || decide (bonus 146 p ≤ bonus 123 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check529 p, rfl⟩
theorem dir146_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 146 169 .southEast || decide (bonus 146 p ≤ bonus 169 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check530 p, rfl⟩
theorem dir146_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 146 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 146 167 .southWest || decide (bonus 146 p ≤ bonus 167 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check531 p, rfl⟩
theorem dir147_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 .north p = true := by
  change ((!walkGuard soko2_2.board support p 147 125 .north || decide (bonus 147 p ≤ bonus 125 p)) && ((PreciseRolling.stayTargets soko2_2.board 125 .north).all (fun landing => !pushGuard support p 147 125 103 landing || decide (bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 125 + bonus 125 (change p 125 (some landing)))) && (pushTargets soko2_2.board 125 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 147 125 103 landing || decide (bonus 147 p ≤ 1 - Generated.soko2_2Potential.boulder 125 - Generated.soko2_2Potential.hole landing + bonus 125 (change p 125 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check532 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check533 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir147_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 .south p = true := by
  change ((!walkGuard soko2_2.board support p 147 169 .south || decide (bonus 147 p ≤ bonus 169 p)) && ((PreciseRolling.stayTargets soko2_2.board 169 .south).all (fun landing => !pushGuard support p 147 169 191 landing || decide (bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some landing)))) && (pushTargets soko2_2.board 169 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 147 169 191 landing || decide (bonus 147 p ≤ 1 - Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.hole landing + bonus 169 (change p 169 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check534 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check535 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir147_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 .east p = true := by
  change ((!walkGuard soko2_2.board support p 147 148 .east || decide (bonus 147 p ≤ bonus 148 p)) && ((PreciseRolling.stayTargets soko2_2.board 148 .east).all (fun landing => !pushGuard support p 147 148 149 landing || decide (bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some landing)))) && (pushTargets soko2_2.board 148 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 147 148 149 landing || decide (bonus 147 p ≤ 1 - Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.hole landing + bonus 148 (change p 148 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check536 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check537 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir147_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 .west p = true := by
  change ((!walkGuard soko2_2.board support p 147 146 .west || decide (bonus 147 p ≤ bonus 146 p)) && ((PreciseRolling.stayTargets soko2_2.board 146 .west).all (fun landing => !pushGuard support p 147 146 145 landing || decide (bonus 147 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some landing)))) && (pushTargets soko2_2.board 146 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 147 146 145 landing || decide (bonus 147 p ≤ 1 - Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.hole landing + bonus 146 (change p 146 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check538 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check539 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir147_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 147 126 .northEast || decide (bonus 147 p ≤ bonus 126 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check540 p, rfl⟩
theorem dir147_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 147 124 .northWest || decide (bonus 147 p ≤ bonus 124 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check541 p, rfl⟩
theorem dir147_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 147 170 .southEast || decide (bonus 147 p ≤ bonus 170 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check542 p, rfl⟩
theorem dir147_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 147 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 147 168 .southWest || decide (bonus 147 p ≤ bonus 168 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check543 p, rfl⟩
theorem dir148_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 .north p = true := by
  change ((!walkGuard soko2_2.board support p 148 126 .north || decide (bonus 148 p ≤ bonus 126 p)) && ((PreciseRolling.stayTargets soko2_2.board 126 .north).all (fun landing => !pushGuard support p 148 126 104 landing || decide (bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 126 + bonus 126 (change p 126 (some landing)))) && (pushTargets soko2_2.board 126 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 148 126 104 landing || decide (bonus 148 p ≤ 1 - Generated.soko2_2Potential.boulder 126 - Generated.soko2_2Potential.hole landing + bonus 126 (change p 126 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check544 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check545 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir148_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 .south p = true := by
  change ((!walkGuard soko2_2.board support p 148 170 .south || decide (bonus 148 p ≤ bonus 170 p)) && ((PreciseRolling.stayTargets soko2_2.board 170 .south).all (fun landing => !pushGuard support p 148 170 192 landing || decide (bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some landing)))) && (pushTargets soko2_2.board 170 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 148 170 192 landing || decide (bonus 148 p ≤ 1 - Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.hole landing + bonus 170 (change p 170 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check546 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check547 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir148_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 .east p = true := by
  change ((!walkGuard soko2_2.board support p 148 149 .east || decide (bonus 148 p ≤ bonus 149 p)) && ((PreciseRolling.stayTargets soko2_2.board 149 .east).all (fun landing => !pushGuard support p 148 149 150 landing || decide (bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some landing)))) && (pushTargets soko2_2.board 149 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 148 149 150 landing || decide (bonus 148 p ≤ 1 - Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.hole landing + bonus 149 (change p 149 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check548 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check549 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir148_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 .west p = true := by
  change ((!walkGuard soko2_2.board support p 148 147 .west || decide (bonus 148 p ≤ bonus 147 p)) && ((PreciseRolling.stayTargets soko2_2.board 147 .west).all (fun landing => !pushGuard support p 148 147 146 landing || decide (bonus 148 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some landing)))) && (pushTargets soko2_2.board 147 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 148 147 146 landing || decide (bonus 148 p ≤ 1 - Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.hole landing + bonus 147 (change p 147 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check550 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check551 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir148_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 148 127 .northEast || decide (bonus 148 p ≤ bonus 127 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check552 p, rfl⟩
theorem dir148_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 148 125 .northWest || decide (bonus 148 p ≤ bonus 125 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check553 p, rfl⟩
theorem dir148_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 148 171 .southEast || decide (bonus 148 p ≤ bonus 171 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check554 p, rfl⟩
theorem dir148_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 148 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 148 169 .southWest || decide (bonus 148 p ≤ bonus 169 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check555 p, rfl⟩
theorem dir149_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 .north p = true := by
  change ((!walkGuard soko2_2.board support p 149 127 .north || decide (bonus 149 p ≤ bonus 127 p)) && ((PreciseRolling.stayTargets soko2_2.board 127 .north).all (fun landing => !pushGuard support p 149 127 105 landing || decide (bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 127 + bonus 127 (change p 127 (some landing)))) && (pushTargets soko2_2.board 127 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 149 127 105 landing || decide (bonus 149 p ≤ 1 - Generated.soko2_2Potential.boulder 127 - Generated.soko2_2Potential.hole landing + bonus 127 (change p 127 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check556 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check557 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir149_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 .south p = true := by
  change ((!walkGuard soko2_2.board support p 149 171 .south || decide (bonus 149 p ≤ bonus 171 p)) && ((PreciseRolling.stayTargets soko2_2.board 171 .south).all (fun landing => !pushGuard support p 149 171 193 landing || decide (bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some landing)))) && (pushTargets soko2_2.board 171 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 149 171 193 landing || decide (bonus 149 p ≤ 1 - Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.hole landing + bonus 171 (change p 171 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check558 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check559 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir149_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 .east p = true := by
  change ((!walkGuard soko2_2.board support p 149 150 .east || decide (bonus 149 p ≤ bonus 150 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check560 p, rfl⟩
theorem dir149_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 .west p = true := by
  change ((!walkGuard soko2_2.board support p 149 148 .west || decide (bonus 149 p ≤ bonus 148 p)) && ((PreciseRolling.stayTargets soko2_2.board 148 .west).all (fun landing => !pushGuard support p 149 148 147 landing || decide (bonus 149 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some landing)))) && (pushTargets soko2_2.board 148 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 149 148 147 landing || decide (bonus 149 p ≤ 1 - Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.hole landing + bonus 148 (change p 148 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check561 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check562 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir149_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 149 128 .northEast || decide (bonus 149 p ≤ bonus 128 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check563 p, rfl⟩
theorem dir149_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 149 126 .northWest || decide (bonus 149 p ≤ bonus 126 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check564 p, rfl⟩
theorem dir149_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 149 172 .southEast || decide (bonus 149 p ≤ bonus 172 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check565 p, rfl⟩
theorem dir149_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 149 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 149 170 .southWest || decide (bonus 149 p ≤ bonus 170 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check566 p, rfl⟩
theorem dir150_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 .north p = true := by
  change ((!walkGuard soko2_2.board support p 150 128 .north || decide (bonus 150 p ≤ bonus 128 p)) && ((PreciseRolling.stayTargets soko2_2.board 128 .north).all (fun landing => !pushGuard support p 150 128 106 landing || decide (bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 128 + bonus 128 (change p 128 (some landing)))) && (pushTargets soko2_2.board 128 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 150 128 106 landing || decide (bonus 150 p ≤ 1 - Generated.soko2_2Potential.boulder 128 - Generated.soko2_2Potential.hole landing + bonus 128 (change p 128 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check567 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check568 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir150_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 .south p = true := by
  change ((!walkGuard soko2_2.board support p 150 172 .south || decide (bonus 150 p ≤ bonus 172 p)) && ((PreciseRolling.stayTargets soko2_2.board 172 .south).all (fun landing => !pushGuard support p 150 172 194 landing || decide (bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 172 + bonus 172 (change p 172 (some landing)))) && (pushTargets soko2_2.board 172 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 150 172 194 landing || decide (bonus 150 p ≤ 1 - Generated.soko2_2Potential.boulder 172 - Generated.soko2_2Potential.hole landing + bonus 172 (change p 172 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check569 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check570 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir150_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 .east p = true := by
  rfl
theorem dir150_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 .west p = true := by
  change ((!walkGuard soko2_2.board support p 150 149 .west || decide (bonus 150 p ≤ bonus 149 p)) && ((PreciseRolling.stayTargets soko2_2.board 149 .west).all (fun landing => !pushGuard support p 150 149 148 landing || decide (bonus 150 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some landing)))) && (pushTargets soko2_2.board 149 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 150 149 148 landing || decide (bonus 150 p ≤ 1 - Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.hole landing + bonus 149 (change p 149 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check571 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check572 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir150_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 .northEast p = true := by
  rfl
theorem dir150_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 150 127 .northWest || decide (bonus 150 p ≤ bonus 127 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check573 p, rfl⟩
theorem dir150_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 .southEast p = true := by
  rfl
theorem dir150_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 150 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 150 171 .southWest || decide (bonus 150 p ≤ bonus 171 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check574 p, rfl⟩
theorem dir155_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 .north p = true := by
  change ((!walkGuard soko2_2.board support p 155 133 .north || decide (bonus 155 p ≤ bonus 133 p)) && ((PreciseRolling.stayTargets soko2_2.board 133 .north).all (fun landing => !pushGuard support p 155 133 111 landing || decide (bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 133 + bonus 133 (change p 133 (some landing)))) && (pushTargets soko2_2.board 133 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 155 133 111 landing || decide (bonus 155 p ≤ 1 - Generated.soko2_2Potential.boulder 133 - Generated.soko2_2Potential.hole landing + bonus 133 (change p 133 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check575 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check576 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir155_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 .south p = true := by
  change ((!walkGuard soko2_2.board support p 155 177 .south || decide (bonus 155 p ≤ bonus 177 p)) && ((PreciseRolling.stayTargets soko2_2.board 177 .south).all (fun landing => !pushGuard support p 155 177 199 landing || decide (bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 177 + bonus 177 (change p 177 (some landing)))) && (pushTargets soko2_2.board 177 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 155 177 199 landing || decide (bonus 155 p ≤ 1 - Generated.soko2_2Potential.boulder 177 - Generated.soko2_2Potential.hole landing + bonus 177 (change p 177 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check577 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check578 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir155_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 .east p = true := by
  change ((!walkGuard soko2_2.board support p 155 156 .east || decide (bonus 155 p ≤ bonus 156 p)) && ((PreciseRolling.stayTargets soko2_2.board 156 .east).all (fun landing => !pushGuard support p 155 156 157 landing || decide (bonus 155 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 156 + bonus 156 (change p 156 (some landing)))) && (pushTargets soko2_2.board 156 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 155 156 157 landing || decide (bonus 155 p ≤ 1 - Generated.soko2_2Potential.boulder 156 - Generated.soko2_2Potential.hole landing + bonus 156 (change p 156 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check579 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check580 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir155_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 .west p = true := by
  rfl
theorem dir155_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 155 134 .northEast || decide (bonus 155 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check581 p, rfl⟩
theorem dir155_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 .northWest p = true := by
  rfl
theorem dir155_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 .southEast p = true := by
  rfl
theorem dir155_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 155 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
