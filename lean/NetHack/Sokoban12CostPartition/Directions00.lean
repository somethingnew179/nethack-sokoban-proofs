import NetHack.Sokoban12CostPartition.ActionBounds048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir29_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 .north p = true := by
  rfl
theorem dir29_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 .south p = true := by
  change ((!walkGuard soko1_2.board support p 29 55 .south || decide (bonus 29 p ≤ bonus 55 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check0 p, rfl⟩
theorem dir29_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 .east p = true := by
  change ((!walkGuard soko1_2.board support p 29 30 .east || decide (bonus 29 p ≤ bonus 30 p)) && ((PreciseRolling.stayTargets soko1_2.board 30 .east).all (fun landing => !pushGuard support p 29 30 31 landing || decide (bonus 29 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 30 + bonus 30 (change p 30 (some landing)))) && (pushTargets soko1_2.board 30 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 29 30 31 landing || decide (bonus 29 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole landing + bonus 30 (change p 30 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check2 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨check3 p, (List.forall_mem_cons.mpr ⟨check4 p, (List.forall_mem_cons.mpr ⟨check5 p, (List.forall_mem_cons.mpr ⟨check6 p, (List.forall_mem_cons.mpr ⟨check7 p, (List.forall_mem_cons.mpr ⟨check8 p, (List.forall_mem_cons.mpr ⟨check9 p, (List.forall_mem_cons.mpr ⟨check10 p, (List.forall_mem_cons.mpr ⟨check11 p, (List.forall_mem_cons.mpr ⟨check12 p, (List.forall_mem_cons.mpr ⟨check13 p, (List.forall_mem_cons.mpr ⟨check14 p, (List.forall_mem_cons.mpr ⟨check15 p, (List.forall_mem_cons.mpr ⟨check16 p, (List.forall_mem_cons.mpr ⟨check17 p, (List.forall_mem_cons.mpr ⟨check18 p, (List.forall_mem_cons.mpr ⟨check19 p, (List.forall_mem_cons.mpr ⟨check20 p, (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem dir29_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 .west p = true := by
  rfl
theorem dir29_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 .northEast p = true := by
  rfl
theorem dir29_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 .northWest p = true := by
  rfl
theorem dir29_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 29 56 .southEast || decide (bonus 29 p ≤ bonus 56 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check21 p, rfl⟩
theorem dir29_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 29 .southWest p = true := by
  rfl
theorem dir30_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 .north p = true := by
  rfl
theorem dir30_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 .south p = true := by
  change ((!walkGuard soko1_2.board support p 30 56 .south || decide (bonus 30 p ≤ bonus 56 p)) && ((PreciseRolling.stayTargets soko1_2.board 56 .south).all (fun landing => !pushGuard support p 30 56 82 landing || decide (bonus 30 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 56 + bonus 56 (change p 56 (some landing)))) && (pushTargets soko1_2.board 56 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 30 56 82 landing || decide (bonus 30 p ≤ 1 - Generated.soko1_2Potential.boulder 56 - Generated.soko1_2Potential.hole landing + bonus 56 (change p 56 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check22 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check23 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir30_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 .east p = true := by
  change ((!walkGuard soko1_2.board support p 30 31 .east || decide (bonus 30 p ≤ bonus 31 p)) && ((PreciseRolling.stayTargets soko1_2.board 31 .east).all (fun landing => !pushGuard support p 30 31 32 landing || decide (bonus 30 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 31 + bonus 31 (change p 31 (some landing)))) && (pushTargets soko1_2.board 31 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 30 31 32 landing || decide (bonus 30 p ≤ 1 - Generated.soko1_2Potential.boulder 31 - Generated.soko1_2Potential.hole landing + bonus 31 (change p 31 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check24 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check25 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check26 p, (by intro cell member; cases member)⟩)
theorem dir30_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 .west p = true := by
  change ((!walkGuard soko1_2.board support p 30 29 .west || decide (bonus 30 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check27 p, rfl⟩
theorem dir30_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 .northEast p = true := by
  rfl
theorem dir30_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 .northWest p = true := by
  rfl
theorem dir30_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 .southEast p = true := by
  rfl
theorem dir30_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 30 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 30 55 .southWest || decide (bonus 30 p ≤ bonus 55 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check28 p, rfl⟩
theorem dir31_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 .north p = true := by
  rfl
theorem dir31_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 .south p = true := by
  rfl
theorem dir31_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 .east p = true := by
  change ((!walkGuard soko1_2.board support p 31 32 .east || decide (bonus 31 p ≤ bonus 32 p)) && ((PreciseRolling.stayTargets soko1_2.board 32 .east).all (fun landing => !pushGuard support p 31 32 33 landing || decide (bonus 31 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 32 + bonus 32 (change p 32 (some landing)))) && (pushTargets soko1_2.board 32 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 31 32 33 landing || decide (bonus 31 p ≤ 1 - Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.hole landing + bonus 32 (change p 32 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check29 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check30 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check31 p, (by intro cell member; cases member)⟩)
theorem dir31_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 .west p = true := by
  change ((!walkGuard soko1_2.board support p 31 30 .west || decide (bonus 31 p ≤ bonus 30 p)) && ((PreciseRolling.stayTargets soko1_2.board 30 .west).all (fun landing => !pushGuard support p 31 30 29 landing || decide (bonus 31 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 30 + bonus 30 (change p 30 (some landing)))) && (pushTargets soko1_2.board 30 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 31 30 29 landing || decide (bonus 31 p ≤ 1 - Generated.soko1_2Potential.boulder 30 - Generated.soko1_2Potential.hole landing + bonus 30 (change p 30 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check32 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check33 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir31_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 .northEast p = true := by
  rfl
theorem dir31_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 .northWest p = true := by
  rfl
theorem dir31_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 .southEast p = true := by
  rfl
theorem dir31_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 31 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 31 56 .southWest || decide (bonus 31 p ≤ bonus 56 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check34 p, rfl⟩
theorem dir32_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 .north p = true := by
  rfl
theorem dir32_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 .south p = true := by
  rfl
theorem dir32_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 .east p = true := by
  change ((!walkGuard soko1_2.board support p 32 33 .east || decide (bonus 32 p ≤ bonus 33 p)) && ((PreciseRolling.stayTargets soko1_2.board 33 .east).all (fun landing => !pushGuard support p 32 33 34 landing || decide (bonus 32 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 33 + bonus 33 (change p 33 (some landing)))) && (pushTargets soko1_2.board 33 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 32 33 34 landing || decide (bonus 32 p ≤ 1 - Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.hole landing + bonus 33 (change p 33 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check35 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check36 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check37 p, (by intro cell member; cases member)⟩)
theorem dir32_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 .west p = true := by
  change ((!walkGuard soko1_2.board support p 32 31 .west || decide (bonus 32 p ≤ bonus 31 p)) && ((PreciseRolling.stayTargets soko1_2.board 31 .west).all (fun landing => !pushGuard support p 32 31 30 landing || decide (bonus 32 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 31 + bonus 31 (change p 31 (some landing)))) && (pushTargets soko1_2.board 31 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 32 31 30 landing || decide (bonus 32 p ≤ 1 - Generated.soko1_2Potential.boulder 31 - Generated.soko1_2Potential.hole landing + bonus 31 (change p 31 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check38 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check39 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir32_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 .northEast p = true := by
  rfl
theorem dir32_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 .northWest p = true := by
  rfl
theorem dir32_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 .southEast p = true := by
  rfl
theorem dir32_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 32 .southWest p = true := by
  rfl
theorem dir33_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 .north p = true := by
  rfl
theorem dir33_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 .south p = true := by
  rfl
theorem dir33_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 .east p = true := by
  change ((!walkGuard soko1_2.board support p 33 34 .east || decide (bonus 33 p ≤ bonus 34 p)) && ((PreciseRolling.stayTargets soko1_2.board 34 .east).all (fun landing => !pushGuard support p 33 34 35 landing || decide (bonus 33 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 34 + bonus 34 (change p 34 (some landing)))) && (pushTargets soko1_2.board 34 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 33 34 35 landing || decide (bonus 33 p ≤ 1 - Generated.soko1_2Potential.boulder 34 - Generated.soko1_2Potential.hole landing + bonus 34 (change p 34 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check40 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check41 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check42 p, (by intro cell member; cases member)⟩)
theorem dir33_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 .west p = true := by
  change ((!walkGuard soko1_2.board support p 33 32 .west || decide (bonus 33 p ≤ bonus 32 p)) && ((PreciseRolling.stayTargets soko1_2.board 32 .west).all (fun landing => !pushGuard support p 33 32 31 landing || decide (bonus 33 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 32 + bonus 32 (change p 32 (some landing)))) && (pushTargets soko1_2.board 32 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 33 32 31 landing || decide (bonus 33 p ≤ 1 - Generated.soko1_2Potential.boulder 32 - Generated.soko1_2Potential.hole landing + bonus 32 (change p 32 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check43 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check44 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check45 p, (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)⟩)⟩)⟩)
theorem dir33_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 .northEast p = true := by
  rfl
theorem dir33_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 .northWest p = true := by
  rfl
theorem dir33_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 .southEast p = true := by
  rfl
theorem dir33_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 33 .southWest p = true := by
  rfl
theorem dir34_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 .north p = true := by
  rfl
theorem dir34_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 .south p = true := by
  rfl
theorem dir34_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 .east p = true := by
  change ((!walkGuard soko1_2.board support p 34 35 .east || decide (bonus 34 p ≤ bonus 35 p)) && ((PreciseRolling.stayTargets soko1_2.board 35 .east).all (fun landing => !pushGuard support p 34 35 36 landing || decide (bonus 34 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 35 + bonus 35 (change p 35 (some landing)))) && (pushTargets soko1_2.board 35 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 34 35 36 landing || decide (bonus 34 p ≤ 1 - Generated.soko1_2Potential.boulder 35 - Generated.soko1_2Potential.hole landing + bonus 35 (change p 35 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check46 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check47 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check48 p, (by intro cell member; cases member)⟩)
theorem dir34_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 .west p = true := by
  change ((!walkGuard soko1_2.board support p 34 33 .west || decide (bonus 34 p ≤ bonus 33 p)) && ((PreciseRolling.stayTargets soko1_2.board 33 .west).all (fun landing => !pushGuard support p 34 33 32 landing || decide (bonus 34 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 33 + bonus 33 (change p 33 (some landing)))) && (pushTargets soko1_2.board 33 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 34 33 32 landing || decide (bonus 34 p ≤ 1 - Generated.soko1_2Potential.boulder 33 - Generated.soko1_2Potential.hole landing + bonus 33 (change p 33 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check49 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check50 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check51 p, (by intro cell member; cases member)⟩)
theorem dir34_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 .northEast p = true := by
  rfl
theorem dir34_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 .northWest p = true := by
  rfl
theorem dir34_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 .southEast p = true := by
  rfl
theorem dir34_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 34 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
