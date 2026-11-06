import NetHack.Sokoban32Refined.Directions09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir131_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 .north p = true := by
  change ((!walkGuard soko3_2.board support p 131 105 .north || decide (bonus 131 p ≤ bonus 105 p)) && ((PreciseRolling.stayTargets soko3_2.board 105 .north).all (fun landing => !pushGuard support p 131 105 79 landing || decide (bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 105 + bonus 105 (change p 105 (some landing)))) && (pushTargets soko3_2.board 105 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 131 105 79 landing || decide (bonus 131 p ≤ 1 - Generated.soko3_2Potential.boulder 105 - Generated.soko3_2Potential.hole landing + bonus 105 (change p 105 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check488 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check489 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir131_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 .south p = true := by
  change ((!walkGuard soko3_2.board support p 131 157 .south || decide (bonus 131 p ≤ bonus 157 p)) && ((PreciseRolling.stayTargets soko3_2.board 157 .south).all (fun landing => !pushGuard support p 131 157 183 landing || decide (bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 157 + bonus 157 (change p 157 (some landing)))) && (pushTargets soko3_2.board 157 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 131 157 183 landing || decide (bonus 131 p ≤ 1 - Generated.soko3_2Potential.boulder 157 - Generated.soko3_2Potential.hole landing + bonus 157 (change p 157 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check490 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check491 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir131_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 .east p = true := by
  change ((!walkGuard soko3_2.board support p 131 132 .east || decide (bonus 131 p ≤ bonus 132 p)) && ((PreciseRolling.stayTargets soko3_2.board 132 .east).all (fun landing => !pushGuard support p 131 132 133 landing || decide (bonus 131 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some landing)))) && (pushTargets soko3_2.board 132 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 131 132 133 landing || decide (bonus 131 p ≤ 1 - Generated.soko3_2Potential.boulder 132 - Generated.soko3_2Potential.hole landing + bonus 132 (change p 132 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check492 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check493 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir131_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 .west p = true := by
  rfl
theorem dir131_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 131 106 .northEast || decide (bonus 131 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check494 p, rfl⟩
theorem dir131_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 .northWest p = true := by
  rfl
theorem dir131_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 131 158 .southEast || decide (bonus 131 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check495 p, rfl⟩
theorem dir131_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 131 .southWest p = true := by
  rfl
theorem dir132_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 .north p = true := by
  change ((!walkGuard soko3_2.board support p 132 106 .north || decide (bonus 132 p ≤ bonus 106 p)) && ((PreciseRolling.stayTargets soko3_2.board 106 .north).all (fun landing => !pushGuard support p 132 106 80 landing || decide (bonus 132 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 106 + bonus 106 (change p 106 (some landing)))) && (pushTargets soko3_2.board 106 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 132 106 80 landing || decide (bonus 132 p ≤ 1 - Generated.soko3_2Potential.boulder 106 - Generated.soko3_2Potential.hole landing + bonus 106 (change p 106 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check496 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check497 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir132_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 .south p = true := by
  change ((!walkGuard soko3_2.board support p 132 158 .south || decide (bonus 132 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check498 p, rfl⟩
theorem dir132_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 .east p = true := by
  change ((!walkGuard soko3_2.board support p 132 133 .east || decide (bonus 132 p ≤ bonus 133 p)) && ((PreciseRolling.stayTargets soko3_2.board 133 .east).all (fun landing => !pushGuard support p 132 133 134 landing || decide (bonus 132 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 133 + bonus 133 (change p 133 (some landing)))) && (pushTargets soko3_2.board 133 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 132 133 134 landing || decide (bonus 132 p ≤ 1 - Generated.soko3_2Potential.boulder 133 - Generated.soko3_2Potential.hole landing + bonus 133 (change p 133 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check499 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check500 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir132_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 .west p = true := by
  change ((!walkGuard soko3_2.board support p 132 131 .west || decide (bonus 132 p ≤ bonus 131 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check501 p, rfl⟩
theorem dir132_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 .northEast p = true := by
  rfl
theorem dir132_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 132 105 .northWest || decide (bonus 132 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check502 p, rfl⟩
theorem dir132_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 132 159 .southEast || decide (bonus 132 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check503 p, rfl⟩
theorem dir132_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 132 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 132 157 .southWest || decide (bonus 132 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check504 p, rfl⟩
theorem dir133_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 .north p = true := by
  rfl
theorem dir133_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 .south p = true := by
  change ((!walkGuard soko3_2.board support p 133 159 .south || decide (bonus 133 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check505 p, rfl⟩
theorem dir133_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 .east p = true := by
  change ((!walkGuard soko3_2.board support p 133 134 .east || decide (bonus 133 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko3_2.board 134 .east).all (fun landing => !pushGuard support p 133 134 135 landing || decide (bonus 133 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko3_2.board 134 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 133 134 135 landing || decide (bonus 133 p ≤ 1 - Generated.soko3_2Potential.boulder 134 - Generated.soko3_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check506 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check507 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir133_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 .west p = true := by
  change ((!walkGuard soko3_2.board support p 133 132 .west || decide (bonus 133 p ≤ bonus 132 p)) && ((PreciseRolling.stayTargets soko3_2.board 132 .west).all (fun landing => !pushGuard support p 133 132 131 landing || decide (bonus 133 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some landing)))) && (pushTargets soko3_2.board 132 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 133 132 131 landing || decide (bonus 133 p ≤ 1 - Generated.soko3_2Potential.boulder 132 - Generated.soko3_2Potential.hole landing + bonus 132 (change p 132 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check508 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check509 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir133_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 133 108 .northEast || decide (bonus 133 p ≤ bonus 108 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check510 p, rfl⟩
theorem dir133_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 133 106 .northWest || decide (bonus 133 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check511 p, rfl⟩
theorem dir133_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 133 160 .southEast || decide (bonus 133 p ≤ bonus 160 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check512 p, rfl⟩
theorem dir133_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 133 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 133 158 .southWest || decide (bonus 133 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check513 p, rfl⟩
theorem dir134_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 .north p = true := by
  change ((!walkGuard soko3_2.board support p 134 108 .north || decide (bonus 134 p ≤ bonus 108 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check514 p, rfl⟩
theorem dir134_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 .south p = true := by
  change ((!walkGuard soko3_2.board support p 134 160 .south || decide (bonus 134 p ≤ bonus 160 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check515 p, rfl⟩
theorem dir134_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 .east p = true := by
  change ((!walkGuard soko3_2.board support p 134 135 .east || decide (bonus 134 p ≤ bonus 135 p)) && ((PreciseRolling.stayTargets soko3_2.board 135 .east).all (fun landing => !pushGuard support p 134 135 136 landing || decide (bonus 134 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some landing)))) && (pushTargets soko3_2.board 135 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 134 135 136 landing || decide (bonus 134 p ≤ 1 - Generated.soko3_2Potential.boulder 135 - Generated.soko3_2Potential.hole landing + bonus 135 (change p 135 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check516 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check517 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir134_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 .west p = true := by
  change ((!walkGuard soko3_2.board support p 134 133 .west || decide (bonus 134 p ≤ bonus 133 p)) && ((PreciseRolling.stayTargets soko3_2.board 133 .west).all (fun landing => !pushGuard support p 134 133 132 landing || decide (bonus 134 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 133 + bonus 133 (change p 133 (some landing)))) && (pushTargets soko3_2.board 133 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 134 133 132 landing || decide (bonus 134 p ≤ 1 - Generated.soko3_2Potential.boulder 133 - Generated.soko3_2Potential.hole landing + bonus 133 (change p 133 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check518 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check519 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir134_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 134 109 .northEast || decide (bonus 134 p ≤ bonus 109 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check520 p, rfl⟩
theorem dir134_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 .northWest p = true := by
  rfl
theorem dir134_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 134 161 .southEast || decide (bonus 134 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check521 p, rfl⟩
theorem dir134_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 134 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 134 159 .southWest || decide (bonus 134 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check522 p, rfl⟩
theorem dir135_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 .north p = true := by
  change ((!walkGuard soko3_2.board support p 135 109 .north || decide (bonus 135 p ≤ bonus 109 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check523 p, rfl⟩
theorem dir135_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 .south p = true := by
  change ((!walkGuard soko3_2.board support p 135 161 .south || decide (bonus 135 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check524 p, rfl⟩
theorem dir135_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 .east p = true := by
  change ((!walkGuard soko3_2.board support p 135 136 .east || decide (bonus 135 p ≤ bonus 136 p)) && ((PreciseRolling.stayTargets soko3_2.board 136 .east).all (fun landing => !pushGuard support p 135 136 137 landing || decide (bonus 135 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some landing)))) && (pushTargets soko3_2.board 136 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 135 136 137 landing || decide (bonus 135 p ≤ 1 - Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.hole landing + bonus 136 (change p 136 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check525 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check526 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir135_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 .west p = true := by
  change ((!walkGuard soko3_2.board support p 135 134 .west || decide (bonus 135 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko3_2.board 134 .west).all (fun landing => !pushGuard support p 135 134 133 landing || decide (bonus 135 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko3_2.board 134 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 135 134 133 landing || decide (bonus 135 p ≤ 1 - Generated.soko3_2Potential.boulder 134 - Generated.soko3_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check527 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check528 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir135_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 135 110 .northEast || decide (bonus 135 p ≤ bonus 110 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check529 p, rfl⟩
theorem dir135_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 135 108 .northWest || decide (bonus 135 p ≤ bonus 108 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check530 p, rfl⟩
theorem dir135_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 135 162 .southEast || decide (bonus 135 p ≤ bonus 162 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check531 p, rfl⟩
theorem dir135_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 135 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 135 160 .southWest || decide (bonus 135 p ≤ bonus 160 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check532 p, rfl⟩
theorem dir136_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 .north p = true := by
  change ((!walkGuard soko3_2.board support p 136 110 .north || decide (bonus 136 p ≤ bonus 110 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check533 p, rfl⟩
theorem dir136_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 .south p = true := by
  change ((!walkGuard soko3_2.board support p 136 162 .south || decide (bonus 136 p ≤ bonus 162 p)) && ((PreciseRolling.stayTargets soko3_2.board 162 .south).all (fun landing => !pushGuard support p 136 162 188 landing || decide (bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some landing)))) && (pushTargets soko3_2.board 162 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 136 162 188 landing || decide (bonus 136 p ≤ 1 - Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.hole landing + bonus 162 (change p 162 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check534 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check535 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir136_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 .east p = true := by
  change ((!walkGuard soko3_2.board support p 136 137 .east || decide (bonus 136 p ≤ bonus 137 p)) && ((PreciseRolling.stayTargets soko3_2.board 137 .east).all (fun landing => !pushGuard support p 136 137 138 landing || decide (bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 137 + bonus 137 (change p 137 (some landing)))) && (pushTargets soko3_2.board 137 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 136 137 138 landing || decide (bonus 136 p ≤ 1 - Generated.soko3_2Potential.boulder 137 - Generated.soko3_2Potential.hole landing + bonus 137 (change p 137 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check536 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check537 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir136_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 .west p = true := by
  change ((!walkGuard soko3_2.board support p 136 135 .west || decide (bonus 136 p ≤ bonus 135 p)) && ((PreciseRolling.stayTargets soko3_2.board 135 .west).all (fun landing => !pushGuard support p 136 135 134 landing || decide (bonus 136 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some landing)))) && (pushTargets soko3_2.board 135 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 136 135 134 landing || decide (bonus 136 p ≤ 1 - Generated.soko3_2Potential.boulder 135 - Generated.soko3_2Potential.hole landing + bonus 135 (change p 135 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check538 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check539 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir136_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 .northEast p = true := by
  rfl
theorem dir136_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 136 109 .northWest || decide (bonus 136 p ≤ bonus 109 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check540 p, rfl⟩
theorem dir136_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 136 163 .southEast || decide (bonus 136 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check541 p, rfl⟩
theorem dir136_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 136 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 136 161 .southWest || decide (bonus 136 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check542 p, rfl⟩
end NetHack.Sokoban32Refined
