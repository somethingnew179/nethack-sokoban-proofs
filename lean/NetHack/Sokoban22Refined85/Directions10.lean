import NetHack.Sokoban22Refined85.Directions09
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir135_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 .north p = true := by
  change ((!walkGuard soko2_2.board support p 135 113 .north || decide (bonus 135 p ≤ bonus 113 p)) && ((PreciseRolling.stayTargets soko2_2.board 113 .north).all (fun landing => !pushGuard support p 135 113 91 landing || decide (bonus 135 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 113 + bonus 113 (change p 113 (some landing)))) && (pushTargets soko2_2.board 113 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 135 113 91 landing || decide (bonus 135 p ≤ 1 - Generated.soko2_2Potential.boulder 113 - Generated.soko2_2Potential.hole landing + bonus 113 (change p 113 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check468 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check469 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir135_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 .south p = true := by
  change ((!walkGuard soko2_2.board support p 135 157 .south || decide (bonus 135 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check470 p, rfl⟩
theorem dir135_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 .east p = true := by
  change ((!walkGuard soko2_2.board support p 135 136 .east || decide (bonus 135 p ≤ bonus 136 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check471 p, rfl⟩
theorem dir135_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 .west p = true := by
  change ((!walkGuard soko2_2.board support p 135 134 .west || decide (bonus 135 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko2_2.board 134 .west).all (fun landing => !pushGuard support p 135 134 133 landing || decide (bonus 135 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko2_2.board 134 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 135 134 133 landing || decide (bonus 135 p ≤ 1 - Generated.soko2_2Potential.boulder 134 - Generated.soko2_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check472 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check473 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir135_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 135 114 .northEast || decide (bonus 135 p ≤ bonus 114 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check474 p, rfl⟩
theorem dir135_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 .northWest p = true := by
  rfl
theorem dir135_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 135 158 .southEast || decide (bonus 135 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check475 p, rfl⟩
theorem dir135_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 135 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 135 156 .southWest || decide (bonus 135 p ≤ bonus 156 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check476 p, rfl⟩
theorem dir136_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 .north p = true := by
  change ((!walkGuard soko2_2.board support p 136 114 .north || decide (bonus 136 p ≤ bonus 114 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check477 p, rfl⟩
theorem dir136_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 .south p = true := by
  change ((!walkGuard soko2_2.board support p 136 158 .south || decide (bonus 136 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko2_2.board 158 .south).all (fun landing => !pushGuard support p 136 158 180 landing || decide (bonus 136 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko2_2.board 158 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 136 158 180 landing || decide (bonus 136 p ≤ 1 - Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check478 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check479 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir136_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 .east p = true := by
  rfl
theorem dir136_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 .west p = true := by
  change ((!walkGuard soko2_2.board support p 136 135 .west || decide (bonus 136 p ≤ bonus 135 p)) && ((PreciseRolling.stayTargets soko2_2.board 135 .west).all (fun landing => !pushGuard support p 136 135 134 landing || decide (bonus 136 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 135 + bonus 135 (change p 135 (some landing)))) && (pushTargets soko2_2.board 135 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 136 135 134 landing || decide (bonus 136 p ≤ 1 - Generated.soko2_2Potential.boulder 135 - Generated.soko2_2Potential.hole landing + bonus 135 (change p 135 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check480 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check481 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir136_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 136 115 .northEast || decide (bonus 136 p ≤ bonus 115 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check482 p, rfl⟩
theorem dir136_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 136 113 .northWest || decide (bonus 136 p ≤ bonus 113 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check483 p, rfl⟩
theorem dir136_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 136 159 .southEast || decide (bonus 136 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check484 p, rfl⟩
theorem dir136_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 136 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 136 157 .southWest || decide (bonus 136 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check485 p, rfl⟩
theorem dir138_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 .north p = true := by
  change ((!walkGuard soko2_2.board support p 138 116 .north || decide (bonus 138 p ≤ bonus 116 p)) && ((PreciseRolling.stayTargets soko2_2.board 116 .north).all (fun landing => !pushGuard support p 138 116 94 landing || decide (bonus 138 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 116 + bonus 116 (change p 116 (some landing)))) && (pushTargets soko2_2.board 116 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 138 116 94 landing || decide (bonus 138 p ≤ 1 - Generated.soko2_2Potential.boulder 116 - Generated.soko2_2Potential.hole landing + bonus 116 (change p 116 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check486 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check487 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir138_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 .south p = true := by
  change ((!walkGuard soko2_2.board support p 138 160 .south || decide (bonus 138 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko2_2.board 160 .south).all (fun landing => !pushGuard support p 138 160 182 landing || decide (bonus 138 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko2_2.board 160 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 138 160 182 landing || decide (bonus 138 p ≤ 1 - Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check488 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check489 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir138_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 .east p = true := by
  rfl
theorem dir138_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 .west p = true := by
  rfl
theorem dir138_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 .northEast p = true := by
  rfl
theorem dir138_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 138 115 .northWest || decide (bonus 138 p ≤ bonus 115 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check490 p, rfl⟩
theorem dir138_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 138 161 .southEast || decide (bonus 138 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check491 p, rfl⟩
theorem dir138_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 138 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 138 159 .southWest || decide (bonus 138 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check492 p, rfl⟩
theorem dir141_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 .north p = true := by
  change ((!walkGuard soko2_2.board support p 141 119 .north || decide (bonus 141 p ≤ bonus 119 p)) && ((PreciseRolling.stayTargets soko2_2.board 119 .north).all (fun landing => !pushGuard support p 141 119 97 landing || decide (bonus 141 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 119 + bonus 119 (change p 119 (some landing)))) && (pushTargets soko2_2.board 119 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 141 119 97 landing || decide (bonus 141 p ≤ 1 - Generated.soko2_2Potential.boulder 119 - Generated.soko2_2Potential.hole landing + bonus 119 (change p 119 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check493 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check494 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir141_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 .south p = true := by
  change ((!walkGuard soko2_2.board support p 141 163 .south || decide (bonus 141 p ≤ bonus 163 p)) && ((PreciseRolling.stayTargets soko2_2.board 163 .south).all (fun landing => !pushGuard support p 141 163 185 landing || decide (bonus 141 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some landing)))) && (pushTargets soko2_2.board 163 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 141 163 185 landing || decide (bonus 141 p ≤ 1 - Generated.soko2_2Potential.boulder 163 - Generated.soko2_2Potential.hole landing + bonus 163 (change p 163 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check495 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check496 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir141_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 .east p = true := by
  rfl
theorem dir141_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 .west p = true := by
  rfl
theorem dir141_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 141 120 .northEast || decide (bonus 141 p ≤ bonus 120 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check497 p, rfl⟩
theorem dir141_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 141 118 .northWest || decide (bonus 141 p ≤ bonus 118 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check498 p, rfl⟩
theorem dir141_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 141 164 .southEast || decide (bonus 141 p ≤ bonus 164 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check499 p, rfl⟩
theorem dir141_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 141 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 141 162 .southWest || decide (bonus 141 p ≤ bonus 162 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check500 p, rfl⟩
theorem dir144_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 .north p = true := by
  change ((!walkGuard soko2_2.board support p 144 122 .north || decide (bonus 144 p ≤ bonus 122 p)) && ((PreciseRolling.stayTargets soko2_2.board 122 .north).all (fun landing => !pushGuard support p 144 122 100 landing || decide (bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 122 + bonus 122 (change p 122 (some landing)))) && (pushTargets soko2_2.board 122 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 144 122 100 landing || decide (bonus 144 p ≤ 1 - Generated.soko2_2Potential.boulder 122 - Generated.soko2_2Potential.hole landing + bonus 122 (change p 122 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check501 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check502 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir144_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 .south p = true := by
  change ((!walkGuard soko2_2.board support p 144 166 .south || decide (bonus 144 p ≤ bonus 166 p)) && ((PreciseRolling.stayTargets soko2_2.board 166 .south).all (fun landing => !pushGuard support p 144 166 188 landing || decide (bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 166 + bonus 166 (change p 166 (some landing)))) && (pushTargets soko2_2.board 166 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 144 166 188 landing || decide (bonus 144 p ≤ 1 - Generated.soko2_2Potential.boulder 166 - Generated.soko2_2Potential.hole landing + bonus 166 (change p 166 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check503 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check504 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir144_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 .east p = true := by
  change ((!walkGuard soko2_2.board support p 144 145 .east || decide (bonus 144 p ≤ bonus 145 p)) && ((PreciseRolling.stayTargets soko2_2.board 145 .east).all (fun landing => !pushGuard support p 144 145 146 landing || decide (bonus 144 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some landing)))) && (pushTargets soko2_2.board 145 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 144 145 146 landing || decide (bonus 144 p ≤ 1 - Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.hole landing + bonus 145 (change p 145 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check505 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check506 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir144_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 .west p = true := by
  rfl
theorem dir144_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 144 123 .northEast || decide (bonus 144 p ≤ bonus 123 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check507 p, rfl⟩
theorem dir144_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 .northWest p = true := by
  rfl
theorem dir144_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 144 167 .southEast || decide (bonus 144 p ≤ bonus 167 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check508 p, rfl⟩
theorem dir144_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 144 .southWest p = true := by
  rfl
theorem dir145_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 .north p = true := by
  change ((!walkGuard soko2_2.board support p 145 123 .north || decide (bonus 145 p ≤ bonus 123 p)) && ((PreciseRolling.stayTargets soko2_2.board 123 .north).all (fun landing => !pushGuard support p 145 123 101 landing || decide (bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 123 + bonus 123 (change p 123 (some landing)))) && (pushTargets soko2_2.board 123 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 145 123 101 landing || decide (bonus 145 p ≤ 1 - Generated.soko2_2Potential.boulder 123 - Generated.soko2_2Potential.hole landing + bonus 123 (change p 123 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check509 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check510 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir145_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 .south p = true := by
  change ((!walkGuard soko2_2.board support p 145 167 .south || decide (bonus 145 p ≤ bonus 167 p)) && ((PreciseRolling.stayTargets soko2_2.board 167 .south).all (fun landing => !pushGuard support p 145 167 189 landing || decide (bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some landing)))) && (pushTargets soko2_2.board 167 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 145 167 189 landing || decide (bonus 145 p ≤ 1 - Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.hole landing + bonus 167 (change p 167 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check511 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check512 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir145_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 .east p = true := by
  change ((!walkGuard soko2_2.board support p 145 146 .east || decide (bonus 145 p ≤ bonus 146 p)) && ((PreciseRolling.stayTargets soko2_2.board 146 .east).all (fun landing => !pushGuard support p 145 146 147 landing || decide (bonus 145 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some landing)))) && (pushTargets soko2_2.board 146 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 145 146 147 landing || decide (bonus 145 p ≤ 1 - Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.hole landing + bonus 146 (change p 146 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check513 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check514 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir145_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 .west p = true := by
  change ((!walkGuard soko2_2.board support p 145 144 .west || decide (bonus 145 p ≤ bonus 144 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check515 p, rfl⟩
theorem dir145_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 145 124 .northEast || decide (bonus 145 p ≤ bonus 124 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check516 p, rfl⟩
theorem dir145_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 145 122 .northWest || decide (bonus 145 p ≤ bonus 122 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check517 p, rfl⟩
theorem dir145_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 145 168 .southEast || decide (bonus 145 p ≤ bonus 168 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check518 p, rfl⟩
theorem dir145_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 145 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 145 166 .southWest || decide (bonus 145 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check519 p, rfl⟩
end NetHack.Sokoban22Refined85
