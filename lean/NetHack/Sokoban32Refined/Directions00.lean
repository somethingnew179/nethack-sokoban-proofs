import NetHack.Sokoban32Refined.ActionBounds056
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir28_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 .north p = true := by
  rfl
theorem dir28_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 .south p = true := by
  change ((!walkGuard soko3_2.board support p 28 54 .south || decide (bonus 28 p ≤ bonus 54 p)) && ((PreciseRolling.stayTargets soko3_2.board 54 .south).all (fun landing => !pushGuard support p 28 54 80 landing || decide (bonus 28 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 54 + bonus 54 (change p 54 (some landing)))) && (pushTargets soko3_2.board 54 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 28 54 80 landing || decide (bonus 28 p ≤ 1 - Generated.soko3_2Potential.boulder 54 - Generated.soko3_2Potential.hole landing + bonus 54 (change p 54 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check0 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir28_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 .east p = true := by
  change ((!walkGuard soko3_2.board support p 28 29 .east || decide (bonus 28 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check2 p, rfl⟩
theorem dir28_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 .west p = true := by
  rfl
theorem dir28_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 .northEast p = true := by
  rfl
theorem dir28_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 .northWest p = true := by
  rfl
theorem dir28_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 28 55 .southEast || decide (bonus 28 p ≤ bonus 55 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check3 p, rfl⟩
theorem dir28_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 28 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 28 53 .southWest || decide (bonus 28 p ≤ bonus 53 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check4 p, rfl⟩
theorem dir29_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 .north p = true := by
  rfl
theorem dir29_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 .south p = true := by
  change ((!walkGuard soko3_2.board support p 29 55 .south || decide (bonus 29 p ≤ bonus 55 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check5 p, rfl⟩
theorem dir29_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 .east p = true := by
  rfl
theorem dir29_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 .west p = true := by
  change ((!walkGuard soko3_2.board support p 29 28 .west || decide (bonus 29 p ≤ bonus 28 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check6 p, rfl⟩
theorem dir29_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 .northEast p = true := by
  rfl
theorem dir29_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 .northWest p = true := by
  rfl
theorem dir29_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 29 56 .southEast || decide (bonus 29 p ≤ bonus 56 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check7 p, rfl⟩
theorem dir29_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 29 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 29 54 .southWest || decide (bonus 29 p ≤ bonus 54 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check8 p, rfl⟩
theorem dir42_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 .north p = true := by
  rfl
theorem dir42_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 .south p = true := by
  change ((!walkGuard soko3_2.board support p 42 68 .south || decide (bonus 42 p ≤ bonus 68 p)) && ((PreciseRolling.stayTargets soko3_2.board 68 .south).all (fun landing => !pushGuard support p 42 68 94 landing || decide (bonus 42 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 68 + bonus 68 (change p 68 (some landing)))) && (pushTargets soko3_2.board 68 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 42 68 94 landing || decide (bonus 42 p ≤ 1 - Generated.soko3_2Potential.boulder 68 - Generated.soko3_2Potential.hole landing + bonus 68 (change p 68 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check9 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check10 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir42_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 .east p = true := by
  change ((!walkGuard soko3_2.board support p 42 43 .east || decide (bonus 42 p ≤ bonus 43 p)) && ((PreciseRolling.stayTargets soko3_2.board 43 .east).all (fun landing => !pushGuard support p 42 43 44 landing || decide (bonus 42 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 43 + bonus 43 (change p 43 (some landing)))) && (pushTargets soko3_2.board 43 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 42 43 44 landing || decide (bonus 42 p ≤ 1 - Generated.soko3_2Potential.boulder 43 - Generated.soko3_2Potential.hole landing + bonus 43 (change p 43 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check11 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check12 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir42_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 .west p = true := by
  rfl
theorem dir42_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 .northEast p = true := by
  rfl
theorem dir42_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 .northWest p = true := by
  rfl
theorem dir42_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 42 69 .southEast || decide (bonus 42 p ≤ bonus 69 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check13 p, rfl⟩
theorem dir42_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 42 .southWest p = true := by
  rfl
theorem dir43_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 .north p = true := by
  rfl
theorem dir43_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 .south p = true := by
  change ((!walkGuard soko3_2.board support p 43 69 .south || decide (bonus 43 p ≤ bonus 69 p)) && ((PreciseRolling.stayTargets soko3_2.board 69 .south).all (fun landing => !pushGuard support p 43 69 95 landing || decide (bonus 43 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some landing)))) && (pushTargets soko3_2.board 69 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 43 69 95 landing || decide (bonus 43 p ≤ 1 - Generated.soko3_2Potential.boulder 69 - Generated.soko3_2Potential.hole landing + bonus 69 (change p 69 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check14 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check15 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir43_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 .east p = true := by
  change ((!walkGuard soko3_2.board support p 43 44 .east || decide (bonus 43 p ≤ bonus 44 p)) && ((PreciseRolling.stayTargets soko3_2.board 44 .east).all (fun landing => !pushGuard support p 43 44 45 landing || decide (bonus 43 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 44 + bonus 44 (change p 44 (some landing)))) && (pushTargets soko3_2.board 44 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 43 44 45 landing || decide (bonus 43 p ≤ 1 - Generated.soko3_2Potential.boulder 44 - Generated.soko3_2Potential.hole landing + bonus 44 (change p 44 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check16 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check17 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir43_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 .west p = true := by
  change ((!walkGuard soko3_2.board support p 43 42 .west || decide (bonus 43 p ≤ bonus 42 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check18 p, rfl⟩
theorem dir43_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 .northEast p = true := by
  rfl
theorem dir43_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 .northWest p = true := by
  rfl
theorem dir43_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 43 70 .southEast || decide (bonus 43 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check19 p, rfl⟩
theorem dir43_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 43 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 43 68 .southWest || decide (bonus 43 p ≤ bonus 68 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check20 p, rfl⟩
theorem dir44_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 .north p = true := by
  rfl
theorem dir44_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 .south p = true := by
  change ((!walkGuard soko3_2.board support p 44 70 .south || decide (bonus 44 p ≤ bonus 70 p)) && ((PreciseRolling.stayTargets soko3_2.board 70 .south).all (fun landing => !pushGuard support p 44 70 96 landing || decide (bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some landing)))) && (pushTargets soko3_2.board 70 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 44 70 96 landing || decide (bonus 44 p ≤ 1 - Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.hole landing + bonus 70 (change p 70 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check21 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check22 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir44_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 .east p = true := by
  change ((!walkGuard soko3_2.board support p 44 45 .east || decide (bonus 44 p ≤ bonus 45 p)) && ((PreciseRolling.stayTargets soko3_2.board 45 .east).all (fun landing => !pushGuard support p 44 45 46 landing || decide (bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 45 + bonus 45 (change p 45 (some landing)))) && (pushTargets soko3_2.board 45 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 44 45 46 landing || decide (bonus 44 p ≤ 1 - Generated.soko3_2Potential.boulder 45 - Generated.soko3_2Potential.hole landing + bonus 45 (change p 45 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check23 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check24 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir44_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 .west p = true := by
  change ((!walkGuard soko3_2.board support p 44 43 .west || decide (bonus 44 p ≤ bonus 43 p)) && ((PreciseRolling.stayTargets soko3_2.board 43 .west).all (fun landing => !pushGuard support p 44 43 42 landing || decide (bonus 44 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 43 + bonus 43 (change p 43 (some landing)))) && (pushTargets soko3_2.board 43 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 44 43 42 landing || decide (bonus 44 p ≤ 1 - Generated.soko3_2Potential.boulder 43 - Generated.soko3_2Potential.hole landing + bonus 43 (change p 43 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check25 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check26 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir44_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 .northEast p = true := by
  rfl
theorem dir44_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 .northWest p = true := by
  rfl
theorem dir44_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 44 71 .southEast || decide (bonus 44 p ≤ bonus 71 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check27 p, rfl⟩
theorem dir44_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 44 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 44 69 .southWest || decide (bonus 44 p ≤ bonus 69 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check28 p, rfl⟩
theorem dir45_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 .north p = true := by
  rfl
theorem dir45_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 .south p = true := by
  change ((!walkGuard soko3_2.board support p 45 71 .south || decide (bonus 45 p ≤ bonus 71 p)) && ((PreciseRolling.stayTargets soko3_2.board 71 .south).all (fun landing => !pushGuard support p 45 71 97 landing || decide (bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some landing)))) && (pushTargets soko3_2.board 71 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 45 71 97 landing || decide (bonus 45 p ≤ 1 - Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.hole landing + bonus 71 (change p 71 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check29 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check30 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir45_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 .east p = true := by
  change ((!walkGuard soko3_2.board support p 45 46 .east || decide (bonus 45 p ≤ bonus 46 p)) && ((PreciseRolling.stayTargets soko3_2.board 46 .east).all (fun landing => !pushGuard support p 45 46 47 landing || decide (bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 46 + bonus 46 (change p 46 (some landing)))) && (pushTargets soko3_2.board 46 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 45 46 47 landing || decide (bonus 45 p ≤ 1 - Generated.soko3_2Potential.boulder 46 - Generated.soko3_2Potential.hole landing + bonus 46 (change p 46 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check31 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check32 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir45_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 .west p = true := by
  change ((!walkGuard soko3_2.board support p 45 44 .west || decide (bonus 45 p ≤ bonus 44 p)) && ((PreciseRolling.stayTargets soko3_2.board 44 .west).all (fun landing => !pushGuard support p 45 44 43 landing || decide (bonus 45 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 44 + bonus 44 (change p 44 (some landing)))) && (pushTargets soko3_2.board 44 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 45 44 43 landing || decide (bonus 45 p ≤ 1 - Generated.soko3_2Potential.boulder 44 - Generated.soko3_2Potential.hole landing + bonus 44 (change p 44 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check33 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check34 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir45_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 .northEast p = true := by
  rfl
theorem dir45_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 .northWest p = true := by
  rfl
theorem dir45_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 45 72 .southEast || decide (bonus 45 p ≤ bonus 72 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check35 p, rfl⟩
theorem dir45_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 45 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 45 70 .southWest || decide (bonus 45 p ≤ bonus 70 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check36 p, rfl⟩
end NetHack.Sokoban32Refined
