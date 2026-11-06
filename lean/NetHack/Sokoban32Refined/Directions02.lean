import NetHack.Sokoban32Refined.Directions01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir54_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 .north p = true := by
  change ((!walkGuard soko3_2.board support p 54 28 .north || decide (bonus 54 p ≤ bonus 28 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check79 p, rfl⟩
theorem dir54_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 .south p = true := by
  change ((!walkGuard soko3_2.board support p 54 80 .south || decide (bonus 54 p ≤ bonus 80 p)) && ((PreciseRolling.stayTargets soko3_2.board 80 .south).all (fun landing => !pushGuard support p 54 80 106 landing || decide (bonus 54 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 80 + bonus 80 (change p 80 (some landing)))) && (pushTargets soko3_2.board 80 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 54 80 106 landing || decide (bonus 54 p ≤ 1 - Generated.soko3_2Potential.boulder 80 - Generated.soko3_2Potential.hole landing + bonus 80 (change p 80 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check80 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check81 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir54_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 .east p = true := by
  change ((!walkGuard soko3_2.board support p 54 55 .east || decide (bonus 54 p ≤ bonus 55 p)) && ((PreciseRolling.stayTargets soko3_2.board 55 .east).all (fun landing => !pushGuard support p 54 55 56 landing || decide (bonus 54 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 55 + bonus 55 (change p 55 (some landing)))) && (pushTargets soko3_2.board 55 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 54 55 56 landing || decide (bonus 54 p ≤ 1 - Generated.soko3_2Potential.boulder 55 - Generated.soko3_2Potential.hole landing + bonus 55 (change p 55 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check82 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check83 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir54_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 .west p = true := by
  change ((!walkGuard soko3_2.board support p 54 53 .west || decide (bonus 54 p ≤ bonus 53 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check84 p, rfl⟩
theorem dir54_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 54 29 .northEast || decide (bonus 54 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check85 p, rfl⟩
theorem dir54_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 .northWest p = true := by
  rfl
theorem dir54_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 .southEast p = true := by
  rfl
theorem dir54_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 54 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 54 79 .southWest || decide (bonus 54 p ≤ bonus 79 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check86 p, rfl⟩
theorem dir55_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 .north p = true := by
  change ((!walkGuard soko3_2.board support p 55 29 .north || decide (bonus 55 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check87 p, rfl⟩
theorem dir55_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 .south p = true := by
  rfl
theorem dir55_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 .east p = true := by
  change ((!walkGuard soko3_2.board support p 55 56 .east || decide (bonus 55 p ≤ bonus 56 p)) && ((PreciseRolling.stayTargets soko3_2.board 56 .east).all (fun landing => !pushGuard support p 55 56 57 landing || decide (bonus 55 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 56 + bonus 56 (change p 56 (some landing)))) && (pushTargets soko3_2.board 56 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 55 56 57 landing || decide (bonus 55 p ≤ 1 - Generated.soko3_2Potential.boulder 56 - Generated.soko3_2Potential.hole landing + bonus 56 (change p 56 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check88 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check89 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir55_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 .west p = true := by
  change ((!walkGuard soko3_2.board support p 55 54 .west || decide (bonus 55 p ≤ bonus 54 p)) && ((PreciseRolling.stayTargets soko3_2.board 54 .west).all (fun landing => !pushGuard support p 55 54 53 landing || decide (bonus 55 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some landing)))) && (pushTargets soko3_2.board 54 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 55 54 53 landing || decide (bonus 55 p ≤ 1 - Generated.soko3_2Potential.boulder 54 - Generated.soko3_2Potential.hole landing + bonus 54 (change p 54 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check90 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check91 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir55_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 .northEast p = true := by
  rfl
theorem dir55_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 55 28 .northWest || decide (bonus 55 p ≤ bonus 28 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check92 p, rfl⟩
theorem dir55_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 .southEast p = true := by
  rfl
theorem dir55_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 55 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 55 80 .southWest || decide (bonus 55 p ≤ bonus 80 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check93 p, rfl⟩
theorem dir56_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 .north p = true := by
  rfl
theorem dir56_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 .south p = true := by
  rfl
theorem dir56_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 .east p = true := by
  change ((!walkGuard soko3_2.board support p 56 57 .east || decide (bonus 56 p ≤ bonus 57 p)) && ((PreciseRolling.stayTargets soko3_2.board 57 .east).all (fun landing => !pushGuard support p 56 57 58 landing || decide (bonus 56 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 57 + bonus 57 (change p 57 (some landing)))) && (pushTargets soko3_2.board 57 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 56 57 58 landing || decide (bonus 56 p ≤ 1 - Generated.soko3_2Potential.boulder 57 - Generated.soko3_2Potential.hole landing + bonus 57 (change p 57 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check94 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check95 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir56_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 .west p = true := by
  change ((!walkGuard soko3_2.board support p 56 55 .west || decide (bonus 56 p ≤ bonus 55 p)) && ((PreciseRolling.stayTargets soko3_2.board 55 .west).all (fun landing => !pushGuard support p 56 55 54 landing || decide (bonus 56 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 55 + bonus 55 (change p 55 (some landing)))) && (pushTargets soko3_2.board 55 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 56 55 54 landing || decide (bonus 56 p ≤ 1 - Generated.soko3_2Potential.boulder 55 - Generated.soko3_2Potential.hole landing + bonus 55 (change p 55 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check96 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check97 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir56_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 .northEast p = true := by
  rfl
theorem dir56_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 56 29 .northWest || decide (bonus 56 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check98 p, rfl⟩
theorem dir56_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 .southEast p = true := by
  rfl
theorem dir56_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 56 .southWest p = true := by
  rfl
theorem dir57_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 .north p = true := by
  rfl
theorem dir57_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 .south p = true := by
  rfl
theorem dir57_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 .east p = true := by
  change ((!walkGuard soko3_2.board support p 57 58 .east || decide (bonus 57 p ≤ bonus 58 p)) && ((PreciseRolling.stayTargets soko3_2.board 58 .east).all (fun landing => !pushGuard support p 57 58 59 landing || decide (bonus 57 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 58 + bonus 58 (change p 58 (some landing)))) && (pushTargets soko3_2.board 58 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 57 58 59 landing || decide (bonus 57 p ≤ 1 - Generated.soko3_2Potential.boulder 58 - Generated.soko3_2Potential.hole landing + bonus 58 (change p 58 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check99 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check100 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir57_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 .west p = true := by
  change ((!walkGuard soko3_2.board support p 57 56 .west || decide (bonus 57 p ≤ bonus 56 p)) && ((PreciseRolling.stayTargets soko3_2.board 56 .west).all (fun landing => !pushGuard support p 57 56 55 landing || decide (bonus 57 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 56 + bonus 56 (change p 56 (some landing)))) && (pushTargets soko3_2.board 56 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 57 56 55 landing || decide (bonus 57 p ≤ 1 - Generated.soko3_2Potential.boulder 56 - Generated.soko3_2Potential.hole landing + bonus 56 (change p 56 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check101 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check102 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir57_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 .northEast p = true := by
  rfl
theorem dir57_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 .northWest p = true := by
  rfl
theorem dir57_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 .southEast p = true := by
  rfl
theorem dir57_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 57 .southWest p = true := by
  rfl
theorem dir58_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 .north p = true := by
  rfl
theorem dir58_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 .south p = true := by
  rfl
theorem dir58_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 .east p = true := by
  change ((!walkGuard soko3_2.board support p 58 59 .east || decide (bonus 58 p ≤ bonus 59 p)) && ((PreciseRolling.stayTargets soko3_2.board 59 .east).all (fun landing => !pushGuard support p 58 59 60 landing || decide (bonus 58 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 59 + bonus 59 (change p 59 (some landing)))) && (pushTargets soko3_2.board 59 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 58 59 60 landing || decide (bonus 58 p ≤ 1 - Generated.soko3_2Potential.boulder 59 - Generated.soko3_2Potential.hole landing + bonus 59 (change p 59 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check103 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check104 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir58_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 .west p = true := by
  change ((!walkGuard soko3_2.board support p 58 57 .west || decide (bonus 58 p ≤ bonus 57 p)) && ((PreciseRolling.stayTargets soko3_2.board 57 .west).all (fun landing => !pushGuard support p 58 57 56 landing || decide (bonus 58 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 57 + bonus 57 (change p 57 (some landing)))) && (pushTargets soko3_2.board 57 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 58 57 56 landing || decide (bonus 58 p ≤ 1 - Generated.soko3_2Potential.boulder 57 - Generated.soko3_2Potential.hole landing + bonus 57 (change p 57 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check105 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check106 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir58_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 .northEast p = true := by
  rfl
theorem dir58_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 .northWest p = true := by
  rfl
theorem dir58_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 .southEast p = true := by
  rfl
theorem dir58_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 58 .southWest p = true := by
  rfl
theorem dir59_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 .north p = true := by
  rfl
theorem dir59_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 .south p = true := by
  rfl
theorem dir59_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 .east p = true := by
  change ((!walkGuard soko3_2.board support p 59 60 .east || decide (bonus 59 p ≤ bonus 60 p)) && ((PreciseRolling.stayTargets soko3_2.board 60 .east).all (fun landing => !pushGuard support p 59 60 61 landing || decide (bonus 59 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 60 + bonus 60 (change p 60 (some landing)))) && (pushTargets soko3_2.board 60 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 59 60 61 landing || decide (bonus 59 p ≤ 1 - Generated.soko3_2Potential.boulder 60 - Generated.soko3_2Potential.hole landing + bonus 60 (change p 60 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check107 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check108 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir59_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 .west p = true := by
  change ((!walkGuard soko3_2.board support p 59 58 .west || decide (bonus 59 p ≤ bonus 58 p)) && ((PreciseRolling.stayTargets soko3_2.board 58 .west).all (fun landing => !pushGuard support p 59 58 57 landing || decide (bonus 59 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 58 + bonus 58 (change p 58 (some landing)))) && (pushTargets soko3_2.board 58 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 59 58 57 landing || decide (bonus 59 p ≤ 1 - Generated.soko3_2Potential.boulder 58 - Generated.soko3_2Potential.hole landing + bonus 58 (change p 58 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check109 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check110 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir59_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 .northEast p = true := by
  rfl
theorem dir59_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 .northWest p = true := by
  rfl
theorem dir59_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 59 86 .southEast || decide (bonus 59 p ≤ bonus 86 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check111 p, rfl⟩
theorem dir59_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 59 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
