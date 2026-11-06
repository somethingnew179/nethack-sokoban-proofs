import NetHack.Sokoban12CostPartition.Directions19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir308_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 .north p = true := by
  change ((!walkGuard soko1_2.board support p 308 282 .north || decide (bonus 308 p ≤ bonus 282 p)) && ((PreciseRolling.stayTargets soko1_2.board 282 .north).all (fun landing => !pushGuard support p 308 282 256 landing || decide (bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 282 + bonus 282 (change p 282 (some landing)))) && (pushTargets soko1_2.board 282 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 308 282 256 landing || decide (bonus 308 p ≤ 1 - Generated.soko1_2Potential.boulder 282 - Generated.soko1_2Potential.hole landing + bonus 282 (change p 282 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check885 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check886 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir308_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 .south p = true := by
  change ((!walkGuard soko1_2.board support p 308 334 .south || decide (bonus 308 p ≤ bonus 334 p)) && ((PreciseRolling.stayTargets soko1_2.board 334 .south).all (fun landing => !pushGuard support p 308 334 360 landing || decide (bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 334 + bonus 334 (change p 334 (some landing)))) && (pushTargets soko1_2.board 334 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 308 334 360 landing || decide (bonus 308 p ≤ 1 - Generated.soko1_2Potential.boulder 334 - Generated.soko1_2Potential.hole landing + bonus 334 (change p 334 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check887 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check888 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir308_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 .east p = true := by
  rfl
theorem dir308_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 .west p = true := by
  change ((!walkGuard soko1_2.board support p 308 307 .west || decide (bonus 308 p ≤ bonus 307 p)) && ((PreciseRolling.stayTargets soko1_2.board 307 .west).all (fun landing => !pushGuard support p 308 307 306 landing || decide (bonus 308 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some landing)))) && (pushTargets soko1_2.board 307 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 308 307 306 landing || decide (bonus 308 p ≤ 1 - Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.hole landing + bonus 307 (change p 307 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check889 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check890 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir308_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 .northEast p = true := by
  rfl
theorem dir308_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 308 281 .northWest || decide (bonus 308 p ≤ bonus 281 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check891 p, rfl⟩
theorem dir308_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 .southEast p = true := by
  rfl
theorem dir308_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 308 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 308 333 .southWest || decide (bonus 308 p ≤ bonus 333 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check892 p, rfl⟩
theorem dir310_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 .north p = true := by
  change ((!walkGuard soko1_2.board support p 310 284 .north || decide (bonus 310 p ≤ bonus 284 p)) && ((PreciseRolling.stayTargets soko1_2.board 284 .north).all (fun landing => !pushGuard support p 310 284 258 landing || decide (bonus 310 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 284 + bonus 284 (change p 284 (some landing)))) && (pushTargets soko1_2.board 284 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 310 284 258 landing || decide (bonus 310 p ≤ 1 - Generated.soko1_2Potential.boulder 284 - Generated.soko1_2Potential.hole landing + bonus 284 (change p 284 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check893 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check894 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir310_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 .south p = true := by
  change ((!walkGuard soko1_2.board support p 310 336 .south || decide (bonus 310 p ≤ bonus 336 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check895 p, rfl⟩
theorem dir310_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 .east p = true := by
  rfl
theorem dir310_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 .west p = true := by
  rfl
theorem dir310_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 .northEast p = true := by
  rfl
theorem dir310_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 .northWest p = true := by
  rfl
theorem dir310_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 .southEast p = true := by
  rfl
theorem dir310_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 310 .southWest p = true := by
  rfl
theorem dir317_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 .north p = true := by
  change ((!walkGuard soko1_2.board support p 317 291 .north || decide (bonus 317 p ≤ bonus 291 p)) && ((PreciseRolling.stayTargets soko1_2.board 291 .north).all (fun landing => !pushGuard support p 317 291 265 landing || decide (bonus 317 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 291 + bonus 291 (change p 291 (some landing)))) && (pushTargets soko1_2.board 291 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 317 291 265 landing || decide (bonus 317 p ≤ 1 - Generated.soko1_2Potential.boulder 291 - Generated.soko1_2Potential.hole landing + bonus 291 (change p 291 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check896 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check897 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir317_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 .south p = true := by
  rfl
theorem dir317_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 .east p = true := by
  change ((!walkGuard soko1_2.board support p 317 318 .east || decide (bonus 317 p ≤ bonus 318 p)) && ((PreciseRolling.stayTargets soko1_2.board 318 .east).all (fun landing => !pushGuard support p 317 318 319 landing || decide (bonus 317 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 318 + bonus 318 (change p 318 (some landing)))) && (pushTargets soko1_2.board 318 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 317 318 319 landing || decide (bonus 317 p ≤ 1 - Generated.soko1_2Potential.boulder 318 - Generated.soko1_2Potential.hole landing + bonus 318 (change p 318 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check898 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check899 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir317_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 .west p = true := by
  rfl
theorem dir317_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 317 292 .northEast || decide (bonus 317 p ≤ bonus 292 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check900 p, rfl⟩
theorem dir317_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 317 290 .northWest || decide (bonus 317 p ≤ bonus 290 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check901 p, rfl⟩
theorem dir317_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 .southEast p = true := by
  rfl
theorem dir317_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 317 .southWest p = true := by
  rfl
theorem dir318_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 .north p = true := by
  change ((!walkGuard soko1_2.board support p 318 292 .north || decide (bonus 318 p ≤ bonus 292 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check902 p, rfl⟩
theorem dir318_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 .south p = true := by
  rfl
theorem dir318_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 .east p = true := by
  change ((!walkGuard soko1_2.board support p 318 319 .east || decide (bonus 318 p ≤ bonus 319 p)) && ((PreciseRolling.stayTargets soko1_2.board 319 .east).all (fun landing => !pushGuard support p 318 319 320 landing || decide (bonus 318 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some landing)))) && (pushTargets soko1_2.board 319 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 318 319 320 landing || decide (bonus 318 p ≤ 1 - Generated.soko1_2Potential.boulder 319 - Generated.soko1_2Potential.hole landing + bonus 319 (change p 319 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check903 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check904 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir318_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 .west p = true := by
  change ((!walkGuard soko1_2.board support p 318 317 .west || decide (bonus 318 p ≤ bonus 317 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check905 p, rfl⟩
theorem dir318_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 318 293 .northEast || decide (bonus 318 p ≤ bonus 293 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check906 p, rfl⟩
theorem dir318_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 318 291 .northWest || decide (bonus 318 p ≤ bonus 291 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check907 p, rfl⟩
theorem dir318_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 318 345 .southEast || decide (bonus 318 p ≤ bonus 345 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check908 p, rfl⟩
theorem dir318_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 318 .southWest p = true := by
  rfl
theorem dir319_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 .north p = true := by
  change ((!walkGuard soko1_2.board support p 319 293 .north || decide (bonus 319 p ≤ bonus 293 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check909 p, rfl⟩
theorem dir319_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 .south p = true := by
  change ((!walkGuard soko1_2.board support p 319 345 .south || decide (bonus 319 p ≤ bonus 345 p)) && ((PreciseRolling.stayTargets soko1_2.board 345 .south).all (fun landing => !pushGuard support p 319 345 371 landing || decide (bonus 319 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 345 + bonus 345 (change p 345 (some landing)))) && (pushTargets soko1_2.board 345 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 319 345 371 landing || decide (bonus 319 p ≤ 1 - Generated.soko1_2Potential.boulder 345 - Generated.soko1_2Potential.hole landing + bonus 345 (change p 345 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check910 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check911 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir319_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 .east p = true := by
  change ((!walkGuard soko1_2.board support p 319 320 .east || decide (bonus 319 p ≤ bonus 320 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check912 p, rfl⟩
theorem dir319_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 .west p = true := by
  change ((!walkGuard soko1_2.board support p 319 318 .west || decide (bonus 319 p ≤ bonus 318 p)) && ((PreciseRolling.stayTargets soko1_2.board 318 .west).all (fun landing => !pushGuard support p 319 318 317 landing || decide (bonus 319 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 318 + bonus 318 (change p 318 (some landing)))) && (pushTargets soko1_2.board 318 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 319 318 317 landing || decide (bonus 319 p ≤ 1 - Generated.soko1_2Potential.boulder 318 - Generated.soko1_2Potential.hole landing + bonus 318 (change p 318 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check913 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check914 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir319_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 319 294 .northEast || decide (bonus 319 p ≤ bonus 294 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check915 p, rfl⟩
theorem dir319_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 319 292 .northWest || decide (bonus 319 p ≤ bonus 292 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check916 p, rfl⟩
theorem dir319_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 .southEast p = true := by
  rfl
theorem dir319_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 319 .southWest p = true := by
  rfl
theorem dir320_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 .north p = true := by
  change ((!walkGuard soko1_2.board support p 320 294 .north || decide (bonus 320 p ≤ bonus 294 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check917 p, rfl⟩
theorem dir320_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 .south p = true := by
  rfl
theorem dir320_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 .east p = true := by
  rfl
theorem dir320_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 .west p = true := by
  change ((!walkGuard soko1_2.board support p 320 319 .west || decide (bonus 320 p ≤ bonus 319 p)) && ((PreciseRolling.stayTargets soko1_2.board 319 .west).all (fun landing => !pushGuard support p 320 319 318 landing || decide (bonus 320 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 319 + bonus 319 (change p 319 (some landing)))) && (pushTargets soko1_2.board 319 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 320 319 318 landing || decide (bonus 320 p ≤ 1 - Generated.soko1_2Potential.boulder 319 - Generated.soko1_2Potential.hole landing + bonus 319 (change p 319 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check918 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check919 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir320_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 .northEast p = true := by
  rfl
theorem dir320_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 320 293 .northWest || decide (bonus 320 p ≤ bonus 293 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check920 p, rfl⟩
theorem dir320_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 .southEast p = true := by
  rfl
theorem dir320_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 320 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 320 345 .southWest || decide (bonus 320 p ≤ bonus 345 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check921 p, rfl⟩
end NetHack.Sokoban12CostPartition
