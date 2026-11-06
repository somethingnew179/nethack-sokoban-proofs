import NetHack.Sokoban22Refined85.Directions13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir169_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 .north p = true := by
  change ((!walkGuard soko2_2.board support p 169 147 .north || decide (bonus 169 p ≤ bonus 147 p)) && ((PreciseRolling.stayTargets soko2_2.board 147 .north).all (fun landing => !pushGuard support p 169 147 125 landing || decide (bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 147 + bonus 147 (change p 147 (some landing)))) && (pushTargets soko2_2.board 147 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 169 147 125 landing || decide (bonus 169 p ≤ 1 - Generated.soko2_2Potential.boulder 147 - Generated.soko2_2Potential.hole landing + bonus 147 (change p 147 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check684 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check685 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir169_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 .south p = true := by
  change ((!walkGuard soko2_2.board support p 169 191 .south || decide (bonus 169 p ≤ bonus 191 p)) && ((PreciseRolling.stayTargets soko2_2.board 191 .south).all (fun landing => !pushGuard support p 169 191 213 landing || decide (bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some landing)))) && (pushTargets soko2_2.board 191 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 169 191 213 landing || decide (bonus 169 p ≤ 1 - Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.hole landing + bonus 191 (change p 191 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check686 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check687 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir169_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 .east p = true := by
  change ((!walkGuard soko2_2.board support p 169 170 .east || decide (bonus 169 p ≤ bonus 170 p)) && ((PreciseRolling.stayTargets soko2_2.board 170 .east).all (fun landing => !pushGuard support p 169 170 171 landing || decide (bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some landing)))) && (pushTargets soko2_2.board 170 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 169 170 171 landing || decide (bonus 169 p ≤ 1 - Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.hole landing + bonus 170 (change p 170 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check688 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check689 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir169_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 .west p = true := by
  change ((!walkGuard soko2_2.board support p 169 168 .west || decide (bonus 169 p ≤ bonus 168 p)) && ((PreciseRolling.stayTargets soko2_2.board 168 .west).all (fun landing => !pushGuard support p 169 168 167 landing || decide (bonus 169 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some landing)))) && (pushTargets soko2_2.board 168 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 169 168 167 landing || decide (bonus 169 p ≤ 1 - Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.hole landing + bonus 168 (change p 168 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check690 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check691 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir169_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 169 148 .northEast || decide (bonus 169 p ≤ bonus 148 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check692 p, rfl⟩
theorem dir169_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 169 146 .northWest || decide (bonus 169 p ≤ bonus 146 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check693 p, rfl⟩
theorem dir169_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 169 192 .southEast || decide (bonus 169 p ≤ bonus 192 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check694 p, rfl⟩
theorem dir169_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 169 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 169 190 .southWest || decide (bonus 169 p ≤ bonus 190 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check695 p, rfl⟩
theorem dir170_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 .north p = true := by
  change ((!walkGuard soko2_2.board support p 170 148 .north || decide (bonus 170 p ≤ bonus 148 p)) && ((PreciseRolling.stayTargets soko2_2.board 148 .north).all (fun landing => !pushGuard support p 170 148 126 landing || decide (bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 148 + bonus 148 (change p 148 (some landing)))) && (pushTargets soko2_2.board 148 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 170 148 126 landing || decide (bonus 170 p ≤ 1 - Generated.soko2_2Potential.boulder 148 - Generated.soko2_2Potential.hole landing + bonus 148 (change p 148 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check696 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check697 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir170_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 .south p = true := by
  change ((!walkGuard soko2_2.board support p 170 192 .south || decide (bonus 170 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko2_2.board 192 .south).all (fun landing => !pushGuard support p 170 192 214 landing || decide (bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko2_2.board 192 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 170 192 214 landing || decide (bonus 170 p ≤ 1 - Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check698 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check699 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir170_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 .east p = true := by
  change ((!walkGuard soko2_2.board support p 170 171 .east || decide (bonus 170 p ≤ bonus 171 p)) && ((PreciseRolling.stayTargets soko2_2.board 171 .east).all (fun landing => !pushGuard support p 170 171 172 landing || decide (bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some landing)))) && (pushTargets soko2_2.board 171 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 170 171 172 landing || decide (bonus 170 p ≤ 1 - Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.hole landing + bonus 171 (change p 171 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check700 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check701 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir170_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 .west p = true := by
  change ((!walkGuard soko2_2.board support p 170 169 .west || decide (bonus 170 p ≤ bonus 169 p)) && ((PreciseRolling.stayTargets soko2_2.board 169 .west).all (fun landing => !pushGuard support p 170 169 168 landing || decide (bonus 170 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some landing)))) && (pushTargets soko2_2.board 169 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 170 169 168 landing || decide (bonus 170 p ≤ 1 - Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.hole landing + bonus 169 (change p 169 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check702 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check703 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir170_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 170 149 .northEast || decide (bonus 170 p ≤ bonus 149 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check704 p, rfl⟩
theorem dir170_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 170 147 .northWest || decide (bonus 170 p ≤ bonus 147 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check705 p, rfl⟩
theorem dir170_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 170 193 .southEast || decide (bonus 170 p ≤ bonus 193 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check706 p, rfl⟩
theorem dir170_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 170 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 170 191 .southWest || decide (bonus 170 p ≤ bonus 191 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check707 p, rfl⟩
theorem dir171_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 .north p = true := by
  change ((!walkGuard soko2_2.board support p 171 149 .north || decide (bonus 171 p ≤ bonus 149 p)) && ((PreciseRolling.stayTargets soko2_2.board 149 .north).all (fun landing => !pushGuard support p 171 149 127 landing || decide (bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 149 + bonus 149 (change p 149 (some landing)))) && (pushTargets soko2_2.board 149 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 171 149 127 landing || decide (bonus 171 p ≤ 1 - Generated.soko2_2Potential.boulder 149 - Generated.soko2_2Potential.hole landing + bonus 149 (change p 149 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check708 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check709 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir171_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 .south p = true := by
  change ((!walkGuard soko2_2.board support p 171 193 .south || decide (bonus 171 p ≤ bonus 193 p)) && ((PreciseRolling.stayTargets soko2_2.board 193 .south).all (fun landing => !pushGuard support p 171 193 215 landing || decide (bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some landing)))) && (pushTargets soko2_2.board 193 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 171 193 215 landing || decide (bonus 171 p ≤ 1 - Generated.soko2_2Potential.boulder 193 - Generated.soko2_2Potential.hole landing + bonus 193 (change p 193 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check710 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check711 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir171_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 .east p = true := by
  change ((!walkGuard soko2_2.board support p 171 172 .east || decide (bonus 171 p ≤ bonus 172 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check712 p, rfl⟩
theorem dir171_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 .west p = true := by
  change ((!walkGuard soko2_2.board support p 171 170 .west || decide (bonus 171 p ≤ bonus 170 p)) && ((PreciseRolling.stayTargets soko2_2.board 170 .west).all (fun landing => !pushGuard support p 171 170 169 landing || decide (bonus 171 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some landing)))) && (pushTargets soko2_2.board 170 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 171 170 169 landing || decide (bonus 171 p ≤ 1 - Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.hole landing + bonus 170 (change p 170 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check713 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check714 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir171_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 171 150 .northEast || decide (bonus 171 p ≤ bonus 150 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check715 p, rfl⟩
theorem dir171_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 171 148 .northWest || decide (bonus 171 p ≤ bonus 148 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check716 p, rfl⟩
theorem dir171_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 171 194 .southEast || decide (bonus 171 p ≤ bonus 194 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check717 p, rfl⟩
theorem dir171_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 171 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 171 192 .southWest || decide (bonus 171 p ≤ bonus 192 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check718 p, rfl⟩
theorem dir172_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 .north p = true := by
  change ((!walkGuard soko2_2.board support p 172 150 .north || decide (bonus 172 p ≤ bonus 150 p)) && ((PreciseRolling.stayTargets soko2_2.board 150 .north).all (fun landing => !pushGuard support p 172 150 128 landing || decide (bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 150 + bonus 150 (change p 150 (some landing)))) && (pushTargets soko2_2.board 150 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 172 150 128 landing || decide (bonus 172 p ≤ 1 - Generated.soko2_2Potential.boulder 150 - Generated.soko2_2Potential.hole landing + bonus 150 (change p 150 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check719 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check720 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir172_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 .south p = true := by
  change ((!walkGuard soko2_2.board support p 172 194 .south || decide (bonus 172 p ≤ bonus 194 p)) && ((PreciseRolling.stayTargets soko2_2.board 194 .south).all (fun landing => !pushGuard support p 172 194 216 landing || decide (bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 194 + bonus 194 (change p 194 (some landing)))) && (pushTargets soko2_2.board 194 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 172 194 216 landing || decide (bonus 172 p ≤ 1 - Generated.soko2_2Potential.boulder 194 - Generated.soko2_2Potential.hole landing + bonus 194 (change p 194 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check721 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check722 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir172_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 .east p = true := by
  rfl
theorem dir172_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 .west p = true := by
  change ((!walkGuard soko2_2.board support p 172 171 .west || decide (bonus 172 p ≤ bonus 171 p)) && ((PreciseRolling.stayTargets soko2_2.board 171 .west).all (fun landing => !pushGuard support p 172 171 170 landing || decide (bonus 172 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some landing)))) && (pushTargets soko2_2.board 171 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 172 171 170 landing || decide (bonus 172 p ≤ 1 - Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.hole landing + bonus 171 (change p 171 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check723 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check724 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir172_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 .northEast p = true := by
  rfl
theorem dir172_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 172 149 .northWest || decide (bonus 172 p ≤ bonus 149 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check725 p, rfl⟩
theorem dir172_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 .southEast p = true := by
  rfl
theorem dir172_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 172 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 172 193 .southWest || decide (bonus 172 p ≤ bonus 193 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check726 p, rfl⟩
theorem dir177_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 .north p = true := by
  change ((!walkGuard soko2_2.board support p 177 155 .north || decide (bonus 177 p ≤ bonus 155 p)) && ((PreciseRolling.stayTargets soko2_2.board 155 .north).all (fun landing => !pushGuard support p 177 155 133 landing || decide (bonus 177 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 155 + bonus 155 (change p 155 (some landing)))) && (pushTargets soko2_2.board 155 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 177 155 133 landing || decide (bonus 177 p ≤ 1 - Generated.soko2_2Potential.boulder 155 - Generated.soko2_2Potential.hole landing + bonus 155 (change p 155 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check727 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check728 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir177_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 .south p = true := by
  change ((!walkGuard soko2_2.board support p 177 199 .south || decide (bonus 177 p ≤ bonus 199 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check729 p, rfl⟩
theorem dir177_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 .east p = true := by
  rfl
theorem dir177_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 .west p = true := by
  rfl
theorem dir177_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 177 156 .northEast || decide (bonus 177 p ≤ bonus 156 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check730 p, rfl⟩
theorem dir177_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 .northWest p = true := by
  rfl
theorem dir177_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 177 200 .southEast || decide (bonus 177 p ≤ bonus 200 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check731 p, rfl⟩
theorem dir177_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 177 .southWest p = true := by
  rfl
theorem dir180_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 .north p = true := by
  change ((!walkGuard soko2_2.board support p 180 158 .north || decide (bonus 180 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko2_2.board 158 .north).all (fun landing => !pushGuard support p 180 158 136 landing || decide (bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko2_2.board 158 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 180 158 136 landing || decide (bonus 180 p ≤ 1 - Generated.soko2_2Potential.boulder 158 - Generated.soko2_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check732 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check733 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir180_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 .south p = true := by
  change ((!walkGuard soko2_2.board support p 180 202 .south || decide (bonus 180 p ≤ bonus 202 p)) && ((PreciseRolling.stayTargets soko2_2.board 202 .south).all (fun landing => !pushGuard support p 180 202 224 landing || decide (bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 202 + bonus 202 (change p 202 (some landing)))) && (pushTargets soko2_2.board 202 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 180 202 224 landing || decide (bonus 180 p ≤ 1 - Generated.soko2_2Potential.boulder 202 - Generated.soko2_2Potential.hole landing + bonus 202 (change p 202 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check734 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check735 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir180_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 .east p = true := by
  change ((!walkGuard soko2_2.board support p 180 181 .east || decide (bonus 180 p ≤ bonus 181 p)) && ((PreciseRolling.stayTargets soko2_2.board 181 .east).all (fun landing => !pushGuard support p 180 181 182 landing || decide (bonus 180 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 181 + bonus 181 (change p 181 (some landing)))) && (pushTargets soko2_2.board 181 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 180 181 182 landing || decide (bonus 180 p ≤ 1 - Generated.soko2_2Potential.boulder 181 - Generated.soko2_2Potential.hole landing + bonus 181 (change p 181 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check736 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check737 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir180_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 .west p = true := by
  rfl
theorem dir180_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 180 159 .northEast || decide (bonus 180 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check738 p, rfl⟩
theorem dir180_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 180 157 .northWest || decide (bonus 180 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check739 p, rfl⟩
theorem dir180_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 .southEast p = true := by
  rfl
theorem dir180_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 180 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 180 201 .southWest || decide (bonus 180 p ≤ bonus 201 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check740 p, rfl⟩
end NetHack.Sokoban22Refined85
