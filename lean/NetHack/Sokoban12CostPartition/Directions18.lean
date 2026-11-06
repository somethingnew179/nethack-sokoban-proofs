import NetHack.Sokoban12CostPartition.Directions17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir289_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 .north p = true := by
  change ((!walkGuard soko1_2.board support p 289 263 .north || decide (bonus 289 p ≤ bonus 263 p)) && ((PreciseRolling.stayTargets soko1_2.board 263 .north).all (fun landing => !pushGuard support p 289 263 237 landing || decide (bonus 289 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some landing)))) && (pushTargets soko1_2.board 263 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 289 263 237 landing || decide (bonus 289 p ≤ 1 - Generated.soko1_2Potential.boulder 263 - Generated.soko1_2Potential.hole landing + bonus 263 (change p 263 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check787 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check788 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir289_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 .south p = true := by
  rfl
theorem dir289_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 .east p = true := by
  change ((!walkGuard soko1_2.board support p 289 290 .east || decide (bonus 289 p ≤ bonus 290 p)) && ((PreciseRolling.stayTargets soko1_2.board 290 .east).all (fun landing => !pushGuard support p 289 290 291 landing || decide (bonus 289 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 290 + bonus 290 (change p 290 (some landing)))) && (pushTargets soko1_2.board 290 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 289 290 291 landing || decide (bonus 289 p ≤ 1 - Generated.soko1_2Potential.boulder 290 - Generated.soko1_2Potential.hole landing + bonus 290 (change p 290 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check789 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check790 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir289_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 .west p = true := by
  change ((!walkGuard soko1_2.board support p 289 288 .west || decide (bonus 289 p ≤ bonus 288 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check791 p, rfl⟩
theorem dir289_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 289 264 .northEast || decide (bonus 289 p ≤ bonus 264 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check792 p, rfl⟩
theorem dir289_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 289 262 .northWest || decide (bonus 289 p ≤ bonus 262 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check793 p, rfl⟩
theorem dir289_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 .southEast p = true := by
  rfl
theorem dir289_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 289 .southWest p = true := by
  rfl
theorem dir290_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 .north p = true := by
  change ((!walkGuard soko1_2.board support p 290 264 .north || decide (bonus 290 p ≤ bonus 264 p)) && ((PreciseRolling.stayTargets soko1_2.board 264 .north).all (fun landing => !pushGuard support p 290 264 238 landing || decide (bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some landing)))) && (pushTargets soko1_2.board 264 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 290 264 238 landing || decide (bonus 290 p ≤ 1 - Generated.soko1_2Potential.boulder 264 - Generated.soko1_2Potential.hole landing + bonus 264 (change p 264 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check794 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check795 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir290_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 .south p = true := by
  rfl
theorem dir290_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 .east p = true := by
  change ((!walkGuard soko1_2.board support p 290 291 .east || decide (bonus 290 p ≤ bonus 291 p)) && ((PreciseRolling.stayTargets soko1_2.board 291 .east).all (fun landing => !pushGuard support p 290 291 292 landing || decide (bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some landing)))) && (pushTargets soko1_2.board 291 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 290 291 292 landing || decide (bonus 290 p ≤ 1 - Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.hole landing + bonus 291 (change p 291 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check796 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check797 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir290_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 .west p = true := by
  change ((!walkGuard soko1_2.board support p 290 289 .west || decide (bonus 290 p ≤ bonus 289 p)) && ((PreciseRolling.stayTargets soko1_2.board 289 .west).all (fun landing => !pushGuard support p 290 289 288 landing || decide (bonus 290 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 289 + bonus 289 (change p 289 (some landing)))) && (pushTargets soko1_2.board 289 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 290 289 288 landing || decide (bonus 290 p ≤ 1 - Generated.soko1_2Potential.boulder 289 - Generated.soko1_2Potential.hole landing + bonus 289 (change p 289 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check798 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check799 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir290_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 290 265 .northEast || decide (bonus 290 p ≤ bonus 265 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check800 p, rfl⟩
theorem dir290_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 290 263 .northWest || decide (bonus 290 p ≤ bonus 263 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check801 p, rfl⟩
theorem dir290_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 290 317 .southEast || decide (bonus 290 p ≤ bonus 317 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check802 p, rfl⟩
theorem dir290_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 290 .southWest p = true := by
  rfl
theorem dir291_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 .north p = true := by
  change ((!walkGuard soko1_2.board support p 291 265 .north || decide (bonus 291 p ≤ bonus 265 p)) && ((PreciseRolling.stayTargets soko1_2.board 265 .north).all (fun landing => !pushGuard support p 291 265 239 landing || decide (bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 265 + bonus 265 (change p 265 (some landing)))) && (pushTargets soko1_2.board 265 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 291 265 239 landing || decide (bonus 291 p ≤ 1 - Generated.soko1_2Potential.boulder 265 - Generated.soko1_2Potential.hole landing + bonus 265 (change p 265 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check803 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check804 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir291_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 .south p = true := by
  change ((!walkGuard soko1_2.board support p 291 317 .south || decide (bonus 291 p ≤ bonus 317 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check805 p, rfl⟩
theorem dir291_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 .east p = true := by
  change ((!walkGuard soko1_2.board support p 291 292 .east || decide (bonus 291 p ≤ bonus 292 p)) && ((PreciseRolling.stayTargets soko1_2.board 292 .east).all (fun landing => !pushGuard support p 291 292 293 landing || decide (bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 292 + bonus 292 (change p 292 (some landing)))) && (pushTargets soko1_2.board 292 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 291 292 293 landing || decide (bonus 291 p ≤ 1 - Generated.soko1_2Potential.boulder 292 - Generated.soko1_2Potential.hole landing + bonus 292 (change p 292 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check806 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check807 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir291_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 .west p = true := by
  change ((!walkGuard soko1_2.board support p 291 290 .west || decide (bonus 291 p ≤ bonus 290 p)) && ((PreciseRolling.stayTargets soko1_2.board 290 .west).all (fun landing => !pushGuard support p 291 290 289 landing || decide (bonus 291 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 290 + bonus 290 (change p 290 (some landing)))) && (pushTargets soko1_2.board 290 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 291 290 289 landing || decide (bonus 291 p ≤ 1 - Generated.soko1_2Potential.boulder 290 - Generated.soko1_2Potential.hole landing + bonus 290 (change p 290 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check808 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check809 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir291_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 .northEast p = true := by
  rfl
theorem dir291_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 291 264 .northWest || decide (bonus 291 p ≤ bonus 264 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check810 p, rfl⟩
theorem dir291_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 291 318 .southEast || decide (bonus 291 p ≤ bonus 318 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check811 p, rfl⟩
theorem dir291_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 291 .southWest p = true := by
  rfl
theorem dir292_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 .north p = true := by
  rfl
theorem dir292_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 .south p = true := by
  change ((!walkGuard soko1_2.board support p 292 318 .south || decide (bonus 292 p ≤ bonus 318 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check812 p, rfl⟩
theorem dir292_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 .east p = true := by
  change ((!walkGuard soko1_2.board support p 292 293 .east || decide (bonus 292 p ≤ bonus 293 p)) && ((PreciseRolling.stayTargets soko1_2.board 293 .east).all (fun landing => !pushGuard support p 292 293 294 landing || decide (bonus 292 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 293 + bonus 293 (change p 293 (some landing)))) && (pushTargets soko1_2.board 293 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 292 293 294 landing || decide (bonus 292 p ≤ 1 - Generated.soko1_2Potential.boulder 293 - Generated.soko1_2Potential.hole landing + bonus 293 (change p 293 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check813 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check814 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir292_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 .west p = true := by
  change ((!walkGuard soko1_2.board support p 292 291 .west || decide (bonus 292 p ≤ bonus 291 p)) && ((PreciseRolling.stayTargets soko1_2.board 291 .west).all (fun landing => !pushGuard support p 292 291 290 landing || decide (bonus 292 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some landing)))) && (pushTargets soko1_2.board 291 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 292 291 290 landing || decide (bonus 292 p ≤ 1 - Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.hole landing + bonus 291 (change p 291 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check815 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check816 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir292_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 .northEast p = true := by
  rfl
theorem dir292_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 292 265 .northWest || decide (bonus 292 p ≤ bonus 265 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check817 p, rfl⟩
theorem dir292_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 292 319 .southEast || decide (bonus 292 p ≤ bonus 319 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check818 p, rfl⟩
theorem dir292_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 292 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 292 317 .southWest || decide (bonus 292 p ≤ bonus 317 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check819 p, rfl⟩
theorem dir293_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 .north p = true := by
  rfl
theorem dir293_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 .south p = true := by
  change ((!walkGuard soko1_2.board support p 293 319 .south || decide (bonus 293 p ≤ bonus 319 p)) && ((PreciseRolling.stayTargets soko1_2.board 319 .south).all (fun landing => !pushGuard support p 293 319 345 landing || decide (bonus 293 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some landing)))) && (pushTargets soko1_2.board 319 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 293 319 345 landing || decide (bonus 293 p ≤ 1 - Generated.soko1_2Potential.boulder 319 - Generated.soko1_2Potential.hole landing + bonus 319 (change p 319 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check820 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check821 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir293_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 .east p = true := by
  change ((!walkGuard soko1_2.board support p 293 294 .east || decide (bonus 293 p ≤ bonus 294 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check822 p, rfl⟩
theorem dir293_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 .west p = true := by
  change ((!walkGuard soko1_2.board support p 293 292 .west || decide (bonus 293 p ≤ bonus 292 p)) && ((PreciseRolling.stayTargets soko1_2.board 292 .west).all (fun landing => !pushGuard support p 293 292 291 landing || decide (bonus 293 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 292 + bonus 292 (change p 292 (some landing)))) && (pushTargets soko1_2.board 292 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 293 292 291 landing || decide (bonus 293 p ≤ 1 - Generated.soko1_2Potential.boulder 292 - Generated.soko1_2Potential.hole landing + bonus 292 (change p 292 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check823 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check824 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir293_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 .northEast p = true := by
  rfl
theorem dir293_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 .northWest p = true := by
  rfl
theorem dir293_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 293 320 .southEast || decide (bonus 293 p ≤ bonus 320 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check825 p, rfl⟩
theorem dir293_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 293 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 293 318 .southWest || decide (bonus 293 p ≤ bonus 318 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check826 p, rfl⟩
theorem dir294_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 .north p = true := by
  rfl
theorem dir294_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 .south p = true := by
  change ((!walkGuard soko1_2.board support p 294 320 .south || decide (bonus 294 p ≤ bonus 320 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check827 p, rfl⟩
theorem dir294_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 .east p = true := by
  rfl
theorem dir294_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 .west p = true := by
  change ((!walkGuard soko1_2.board support p 294 293 .west || decide (bonus 294 p ≤ bonus 293 p)) && ((PreciseRolling.stayTargets soko1_2.board 293 .west).all (fun landing => !pushGuard support p 294 293 292 landing || decide (bonus 294 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 293 + bonus 293 (change p 293 (some landing)))) && (pushTargets soko1_2.board 293 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 294 293 292 landing || decide (bonus 294 p ≤ 1 - Generated.soko1_2Potential.boulder 293 - Generated.soko1_2Potential.hole landing + bonus 293 (change p 293 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check828 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check829 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir294_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 .northEast p = true := by
  rfl
theorem dir294_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 .northWest p = true := by
  rfl
theorem dir294_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 .southEast p = true := by
  rfl
theorem dir294_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 294 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 294 319 .southWest || decide (bonus 294 p ≤ bonus 319 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check830 p, rfl⟩
end NetHack.Sokoban12CostPartition
