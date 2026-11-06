import NetHack.Sokoban32Refined.Directions12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir157_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 .north p = true := by
  change ((!walkGuard soko3_2.board support p 157 131 .north || decide (bonus 157 p ≤ bonus 131 p)) && ((PreciseRolling.stayTargets soko3_2.board 131 .north).all (fun landing => !pushGuard support p 157 131 105 landing || decide (bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 131 + bonus 131 (change p 131 (some landing)))) && (pushTargets soko3_2.board 131 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 157 131 105 landing || decide (bonus 157 p ≤ 1 - Generated.soko3_2Potential.boulder 131 - Generated.soko3_2Potential.hole landing + bonus 131 (change p 131 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check665 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check666 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir157_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 .south p = true := by
  change ((!walkGuard soko3_2.board support p 157 183 .south || decide (bonus 157 p ≤ bonus 183 p)) && ((PreciseRolling.stayTargets soko3_2.board 183 .south).all (fun landing => !pushGuard support p 157 183 209 landing || decide (bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 183 + bonus 183 (change p 183 (some landing)))) && (pushTargets soko3_2.board 183 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 157 183 209 landing || decide (bonus 157 p ≤ 1 - Generated.soko3_2Potential.boulder 183 - Generated.soko3_2Potential.hole landing + bonus 183 (change p 183 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check667 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check668 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir157_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 .east p = true := by
  change ((!walkGuard soko3_2.board support p 157 158 .east || decide (bonus 157 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko3_2.board 158 .east).all (fun landing => !pushGuard support p 157 158 159 landing || decide (bonus 157 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko3_2.board 158 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 157 158 159 landing || decide (bonus 157 p ≤ 1 - Generated.soko3_2Potential.boulder 158 - Generated.soko3_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check669 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check670 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir157_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 .west p = true := by
  rfl
theorem dir157_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 157 132 .northEast || decide (bonus 157 p ≤ bonus 132 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check671 p, rfl⟩
theorem dir157_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 .northWest p = true := by
  rfl
theorem dir157_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 .southEast p = true := by
  rfl
theorem dir157_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 157 .southWest p = true := by
  rfl
theorem dir158_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 .north p = true := by
  change ((!walkGuard soko3_2.board support p 158 132 .north || decide (bonus 158 p ≤ bonus 132 p)) && ((PreciseRolling.stayTargets soko3_2.board 132 .north).all (fun landing => !pushGuard support p 158 132 106 landing || decide (bonus 158 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 132 + bonus 132 (change p 132 (some landing)))) && (pushTargets soko3_2.board 132 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 158 132 106 landing || decide (bonus 158 p ≤ 1 - Generated.soko3_2Potential.boulder 132 - Generated.soko3_2Potential.hole landing + bonus 132 (change p 132 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check672 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check673 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 .south p = true := by
  rfl
theorem dir158_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 .east p = true := by
  change ((!walkGuard soko3_2.board support p 158 159 .east || decide (bonus 158 p ≤ bonus 159 p)) && ((PreciseRolling.stayTargets soko3_2.board 159 .east).all (fun landing => !pushGuard support p 158 159 160 landing || decide (bonus 158 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 159 + bonus 159 (change p 159 (some landing)))) && (pushTargets soko3_2.board 159 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 158 159 160 landing || decide (bonus 158 p ≤ 1 - Generated.soko3_2Potential.boulder 159 - Generated.soko3_2Potential.hole landing + bonus 159 (change p 159 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check674 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check675 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 .west p = true := by
  change ((!walkGuard soko3_2.board support p 158 157 .west || decide (bonus 158 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check676 p, rfl⟩
theorem dir158_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 158 133 .northEast || decide (bonus 158 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check677 p, rfl⟩
theorem dir158_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 158 131 .northWest || decide (bonus 158 p ≤ bonus 131 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check678 p, rfl⟩
theorem dir158_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 .southEast p = true := by
  rfl
theorem dir158_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 158 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 158 183 .southWest || decide (bonus 158 p ≤ bonus 183 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check679 p, rfl⟩
theorem dir159_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 .north p = true := by
  change ((!walkGuard soko3_2.board support p 159 133 .north || decide (bonus 159 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check680 p, rfl⟩
theorem dir159_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 .south p = true := by
  rfl
theorem dir159_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 .east p = true := by
  change ((!walkGuard soko3_2.board support p 159 160 .east || decide (bonus 159 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko3_2.board 160 .east).all (fun landing => !pushGuard support p 159 160 161 landing || decide (bonus 159 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko3_2.board 160 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 159 160 161 landing || decide (bonus 159 p ≤ 1 - Generated.soko3_2Potential.boulder 160 - Generated.soko3_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check681 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check682 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir159_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 .west p = true := by
  change ((!walkGuard soko3_2.board support p 159 158 .west || decide (bonus 159 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko3_2.board 158 .west).all (fun landing => !pushGuard support p 159 158 157 landing || decide (bonus 159 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko3_2.board 158 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 159 158 157 landing || decide (bonus 159 p ≤ 1 - Generated.soko3_2Potential.boulder 158 - Generated.soko3_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check683 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check684 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir159_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 159 134 .northEast || decide (bonus 159 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check685 p, rfl⟩
theorem dir159_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 159 132 .northWest || decide (bonus 159 p ≤ bonus 132 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check686 p, rfl⟩
theorem dir159_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 .southEast p = true := by
  rfl
theorem dir159_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 159 .southWest p = true := by
  rfl
theorem dir160_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 .north p = true := by
  change ((!walkGuard soko3_2.board support p 160 134 .north || decide (bonus 160 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko3_2.board 134 .north).all (fun landing => !pushGuard support p 160 134 108 landing || decide (bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko3_2.board 134 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 160 134 108 landing || decide (bonus 160 p ≤ 1 - Generated.soko3_2Potential.boulder 134 - Generated.soko3_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check687 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check688 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 .south p = true := by
  rfl
theorem dir160_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 .east p = true := by
  change ((!walkGuard soko3_2.board support p 160 161 .east || decide (bonus 160 p ≤ bonus 161 p)) && ((PreciseRolling.stayTargets soko3_2.board 161 .east).all (fun landing => !pushGuard support p 160 161 162 landing || decide (bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 161 + bonus 161 (change p 161 (some landing)))) && (pushTargets soko3_2.board 161 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 160 161 162 landing || decide (bonus 160 p ≤ 1 - Generated.soko3_2Potential.boulder 161 - Generated.soko3_2Potential.hole landing + bonus 161 (change p 161 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check689 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check690 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 .west p = true := by
  change ((!walkGuard soko3_2.board support p 160 159 .west || decide (bonus 160 p ≤ bonus 159 p)) && ((PreciseRolling.stayTargets soko3_2.board 159 .west).all (fun landing => !pushGuard support p 160 159 158 landing || decide (bonus 160 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 159 + bonus 159 (change p 159 (some landing)))) && (pushTargets soko3_2.board 159 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 160 159 158 landing || decide (bonus 160 p ≤ 1 - Generated.soko3_2Potential.boulder 159 - Generated.soko3_2Potential.hole landing + bonus 159 (change p 159 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check691 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check692 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 160 135 .northEast || decide (bonus 160 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check693 p, rfl⟩
theorem dir160_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 160 133 .northWest || decide (bonus 160 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check694 p, rfl⟩
theorem dir160_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 .southEast p = true := by
  rfl
theorem dir160_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 160 .southWest p = true := by
  rfl
theorem dir161_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 .north p = true := by
  change ((!walkGuard soko3_2.board support p 161 135 .north || decide (bonus 161 p ≤ bonus 135 p)) && ((PreciseRolling.stayTargets soko3_2.board 135 .north).all (fun landing => !pushGuard support p 161 135 109 landing || decide (bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 135 + bonus 135 (change p 135 (some landing)))) && (pushTargets soko3_2.board 135 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 161 135 109 landing || decide (bonus 161 p ≤ 1 - Generated.soko3_2Potential.boulder 135 - Generated.soko3_2Potential.hole landing + bonus 135 (change p 135 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check695 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check696 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir161_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 .south p = true := by
  rfl
theorem dir161_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 .east p = true := by
  change ((!walkGuard soko3_2.board support p 161 162 .east || decide (bonus 161 p ≤ bonus 162 p)) && ((PreciseRolling.stayTargets soko3_2.board 162 .east).all (fun landing => !pushGuard support p 161 162 163 landing || decide (bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some landing)))) && (pushTargets soko3_2.board 162 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 161 162 163 landing || decide (bonus 161 p ≤ 1 - Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.hole landing + bonus 162 (change p 162 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check697 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check698 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir161_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 .west p = true := by
  change ((!walkGuard soko3_2.board support p 161 160 .west || decide (bonus 161 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko3_2.board 160 .west).all (fun landing => !pushGuard support p 161 160 159 landing || decide (bonus 161 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko3_2.board 160 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 161 160 159 landing || decide (bonus 161 p ≤ 1 - Generated.soko3_2Potential.boulder 160 - Generated.soko3_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check699 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check700 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir161_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 161 136 .northEast || decide (bonus 161 p ≤ bonus 136 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check701 p, rfl⟩
theorem dir161_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 161 134 .northWest || decide (bonus 161 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check702 p, rfl⟩
theorem dir161_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 161 188 .southEast || decide (bonus 161 p ≤ bonus 188 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check703 p, rfl⟩
theorem dir161_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 161 .southWest p = true := by
  rfl
theorem dir162_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 .north p = true := by
  change ((!walkGuard soko3_2.board support p 162 136 .north || decide (bonus 162 p ≤ bonus 136 p)) && ((PreciseRolling.stayTargets soko3_2.board 136 .north).all (fun landing => !pushGuard support p 162 136 110 landing || decide (bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 136 + bonus 136 (change p 136 (some landing)))) && (pushTargets soko3_2.board 136 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 162 136 110 landing || decide (bonus 162 p ≤ 1 - Generated.soko3_2Potential.boulder 136 - Generated.soko3_2Potential.hole landing + bonus 136 (change p 136 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check704 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check705 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir162_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 .south p = true := by
  change ((!walkGuard soko3_2.board support p 162 188 .south || decide (bonus 162 p ≤ bonus 188 p)) && ((PreciseRolling.stayTargets soko3_2.board 188 .south).all (fun landing => !pushGuard support p 162 188 214 landing || decide (bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 188 + bonus 188 (change p 188 (some landing)))) && (pushTargets soko3_2.board 188 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 162 188 214 landing || decide (bonus 162 p ≤ 1 - Generated.soko3_2Potential.boulder 188 - Generated.soko3_2Potential.hole landing + bonus 188 (change p 188 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check706 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check707 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir162_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 .east p = true := by
  change ((!walkGuard soko3_2.board support p 162 163 .east || decide (bonus 162 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check708 p, rfl⟩
theorem dir162_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 .west p = true := by
  change ((!walkGuard soko3_2.board support p 162 161 .west || decide (bonus 162 p ≤ bonus 161 p)) && ((PreciseRolling.stayTargets soko3_2.board 161 .west).all (fun landing => !pushGuard support p 162 161 160 landing || decide (bonus 162 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 161 + bonus 161 (change p 161 (some landing)))) && (pushTargets soko3_2.board 161 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 162 161 160 landing || decide (bonus 162 p ≤ 1 - Generated.soko3_2Potential.boulder 161 - Generated.soko3_2Potential.hole landing + bonus 161 (change p 161 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check709 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check710 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir162_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 162 137 .northEast || decide (bonus 162 p ≤ bonus 137 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check711 p, rfl⟩
theorem dir162_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 162 135 .northWest || decide (bonus 162 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check712 p, rfl⟩
theorem dir162_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 162 189 .southEast || decide (bonus 162 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check713 p, rfl⟩
theorem dir162_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 162 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
