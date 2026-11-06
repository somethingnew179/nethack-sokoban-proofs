import NetHack.Sokoban12CostPartition.Directions16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir279_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 .north p = true := by
  change ((!walkGuard soko1_2.board support p 279 253 .north || decide (bonus 279 p ≤ bonus 253 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check740 p, rfl⟩
theorem dir279_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 .south p = true := by
  change ((!walkGuard soko1_2.board support p 279 305 .south || decide (bonus 279 p ≤ bonus 305 p)) && ((PreciseRolling.stayTargets soko1_2.board 305 .south).all (fun landing => !pushGuard support p 279 305 331 landing || decide (bonus 279 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 305 + bonus 305 (change p 305 (some landing)))) && (pushTargets soko1_2.board 305 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 279 305 331 landing || decide (bonus 279 p ≤ 1 - Generated.soko1_2Potential.boulder 305 - Generated.soko1_2Potential.hole landing + bonus 305 (change p 305 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check741 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check742 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir279_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 .east p = true := by
  change ((!walkGuard soko1_2.board support p 279 280 .east || decide (bonus 279 p ≤ bonus 280 p)) && ((PreciseRolling.stayTargets soko1_2.board 280 .east).all (fun landing => !pushGuard support p 279 280 281 landing || decide (bonus 279 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some landing)))) && (pushTargets soko1_2.board 280 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 279 280 281 landing || decide (bonus 279 p ≤ 1 - Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.hole landing + bonus 280 (change p 280 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check743 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check744 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir279_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 .west p = true := by
  change ((!walkGuard soko1_2.board support p 279 278 .west || decide (bonus 279 p ≤ bonus 278 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check745 p, rfl⟩
theorem dir279_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 279 254 .northEast || decide (bonus 279 p ≤ bonus 254 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check746 p, rfl⟩
theorem dir279_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 279 252 .northWest || decide (bonus 279 p ≤ bonus 252 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check747 p, rfl⟩
theorem dir279_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 279 306 .southEast || decide (bonus 279 p ≤ bonus 306 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check748 p, rfl⟩
theorem dir279_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 279 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 279 304 .southWest || decide (bonus 279 p ≤ bonus 304 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check749 p, rfl⟩
theorem dir280_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 .north p = true := by
  change ((!walkGuard soko1_2.board support p 280 254 .north || decide (bonus 280 p ≤ bonus 254 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check750 p, rfl⟩
theorem dir280_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 .south p = true := by
  change ((!walkGuard soko1_2.board support p 280 306 .south || decide (bonus 280 p ≤ bonus 306 p)) && ((PreciseRolling.stayTargets soko1_2.board 306 .south).all (fun landing => !pushGuard support p 280 306 332 landing || decide (bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 306 + bonus 306 (change p 306 (some landing)))) && (pushTargets soko1_2.board 306 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 280 306 332 landing || decide (bonus 280 p ≤ 1 - Generated.soko1_2Potential.boulder 306 - Generated.soko1_2Potential.hole landing + bonus 306 (change p 306 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check751 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check752 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir280_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 .east p = true := by
  change ((!walkGuard soko1_2.board support p 280 281 .east || decide (bonus 280 p ≤ bonus 281 p)) && ((PreciseRolling.stayTargets soko1_2.board 281 .east).all (fun landing => !pushGuard support p 280 281 282 landing || decide (bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some landing)))) && (pushTargets soko1_2.board 281 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 280 281 282 landing || decide (bonus 280 p ≤ 1 - Generated.soko1_2Potential.boulder 281 - Generated.soko1_2Potential.hole landing + bonus 281 (change p 281 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check753 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check754 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir280_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 .west p = true := by
  change ((!walkGuard soko1_2.board support p 280 279 .west || decide (bonus 280 p ≤ bonus 279 p)) && ((PreciseRolling.stayTargets soko1_2.board 279 .west).all (fun landing => !pushGuard support p 280 279 278 landing || decide (bonus 280 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 279 + bonus 279 (change p 279 (some landing)))) && (pushTargets soko1_2.board 279 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 280 279 278 landing || decide (bonus 280 p ≤ 1 - Generated.soko1_2Potential.boulder 279 - Generated.soko1_2Potential.hole landing + bonus 279 (change p 279 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check755 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check756 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir280_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 280 255 .northEast || decide (bonus 280 p ≤ bonus 255 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check757 p, rfl⟩
theorem dir280_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 280 253 .northWest || decide (bonus 280 p ≤ bonus 253 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check758 p, rfl⟩
theorem dir280_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 280 307 .southEast || decide (bonus 280 p ≤ bonus 307 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check759 p, rfl⟩
theorem dir280_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 280 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 280 305 .southWest || decide (bonus 280 p ≤ bonus 305 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check760 p, rfl⟩
theorem dir281_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 .north p = true := by
  change ((!walkGuard soko1_2.board support p 281 255 .north || decide (bonus 281 p ≤ bonus 255 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check761 p, rfl⟩
theorem dir281_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 .south p = true := by
  change ((!walkGuard soko1_2.board support p 281 307 .south || decide (bonus 281 p ≤ bonus 307 p)) && ((PreciseRolling.stayTargets soko1_2.board 307 .south).all (fun landing => !pushGuard support p 281 307 333 landing || decide (bonus 281 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 307 + bonus 307 (change p 307 (some landing)))) && (pushTargets soko1_2.board 307 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 281 307 333 landing || decide (bonus 281 p ≤ 1 - Generated.soko1_2Potential.boulder 307 - Generated.soko1_2Potential.hole landing + bonus 307 (change p 307 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check762 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check763 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir281_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 .east p = true := by
  change ((!walkGuard soko1_2.board support p 281 282 .east || decide (bonus 281 p ≤ bonus 282 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check764 p, rfl⟩
theorem dir281_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 .west p = true := by
  change ((!walkGuard soko1_2.board support p 281 280 .west || decide (bonus 281 p ≤ bonus 280 p)) && ((PreciseRolling.stayTargets soko1_2.board 280 .west).all (fun landing => !pushGuard support p 281 280 279 landing || decide (bonus 281 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 280 + bonus 280 (change p 280 (some landing)))) && (pushTargets soko1_2.board 280 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 281 280 279 landing || decide (bonus 281 p ≤ 1 - Generated.soko1_2Potential.boulder 280 - Generated.soko1_2Potential.hole landing + bonus 280 (change p 280 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check765 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check766 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir281_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 281 256 .northEast || decide (bonus 281 p ≤ bonus 256 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check767 p, rfl⟩
theorem dir281_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 281 254 .northWest || decide (bonus 281 p ≤ bonus 254 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check768 p, rfl⟩
theorem dir281_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 281 308 .southEast || decide (bonus 281 p ≤ bonus 308 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check769 p, rfl⟩
theorem dir281_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 281 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 281 306 .southWest || decide (bonus 281 p ≤ bonus 306 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check770 p, rfl⟩
theorem dir282_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 .north p = true := by
  change ((!walkGuard soko1_2.board support p 282 256 .north || decide (bonus 282 p ≤ bonus 256 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check771 p, rfl⟩
theorem dir282_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 .south p = true := by
  change ((!walkGuard soko1_2.board support p 282 308 .south || decide (bonus 282 p ≤ bonus 308 p)) && ((PreciseRolling.stayTargets soko1_2.board 308 .south).all (fun landing => !pushGuard support p 282 308 334 landing || decide (bonus 282 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 308 + bonus 308 (change p 308 (some landing)))) && (pushTargets soko1_2.board 308 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 282 308 334 landing || decide (bonus 282 p ≤ 1 - Generated.soko1_2Potential.boulder 308 - Generated.soko1_2Potential.hole landing + bonus 308 (change p 308 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check772 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check773 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir282_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 .east p = true := by
  rfl
theorem dir282_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 .west p = true := by
  change ((!walkGuard soko1_2.board support p 282 281 .west || decide (bonus 282 p ≤ bonus 281 p)) && ((PreciseRolling.stayTargets soko1_2.board 281 .west).all (fun landing => !pushGuard support p 282 281 280 landing || decide (bonus 282 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some landing)))) && (pushTargets soko1_2.board 281 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 282 281 280 landing || decide (bonus 282 p ≤ 1 - Generated.soko1_2Potential.boulder 281 - Generated.soko1_2Potential.hole landing + bonus 281 (change p 281 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check774 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check775 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir282_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 .northEast p = true := by
  rfl
theorem dir282_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 282 255 .northWest || decide (bonus 282 p ≤ bonus 255 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check776 p, rfl⟩
theorem dir282_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 .southEast p = true := by
  rfl
theorem dir282_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 282 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 282 307 .southWest || decide (bonus 282 p ≤ bonus 307 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check777 p, rfl⟩
theorem dir284_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 .north p = true := by
  change ((!walkGuard soko1_2.board support p 284 258 .north || decide (bonus 284 p ≤ bonus 258 p)) && ((PreciseRolling.stayTargets soko1_2.board 258 .north).all (fun landing => !pushGuard support p 284 258 232 landing || decide (bonus 284 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 258 + bonus 258 (change p 258 (some landing)))) && (pushTargets soko1_2.board 258 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 284 258 232 landing || decide (bonus 284 p ≤ 1 - Generated.soko1_2Potential.boulder 258 - Generated.soko1_2Potential.hole landing + bonus 258 (change p 258 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check778 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check779 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir284_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 .south p = true := by
  change ((!walkGuard soko1_2.board support p 284 310 .south || decide (bonus 284 p ≤ bonus 310 p)) && ((PreciseRolling.stayTargets soko1_2.board 310 .south).all (fun landing => !pushGuard support p 284 310 336 landing || decide (bonus 284 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 310 + bonus 310 (change p 310 (some landing)))) && (pushTargets soko1_2.board 310 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 284 310 336 landing || decide (bonus 284 p ≤ 1 - Generated.soko1_2Potential.boulder 310 - Generated.soko1_2Potential.hole landing + bonus 310 (change p 310 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check780 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check781 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir284_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 .east p = true := by
  rfl
theorem dir284_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 .west p = true := by
  rfl
theorem dir284_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 .northEast p = true := by
  rfl
theorem dir284_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 .northWest p = true := by
  rfl
theorem dir284_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 .southEast p = true := by
  rfl
theorem dir284_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 284 .southWest p = true := by
  rfl
theorem dir288_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 .north p = true := by
  change ((!walkGuard soko1_2.board support p 288 262 .north || decide (bonus 288 p ≤ bonus 262 p)) && ((PreciseRolling.stayTargets soko1_2.board 262 .north).all (fun landing => !pushGuard support p 288 262 236 landing || decide (bonus 288 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 262 + bonus 262 (change p 262 (some landing)))) && (pushTargets soko1_2.board 262 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 288 262 236 landing || decide (bonus 288 p ≤ 1 - Generated.soko1_2Potential.boulder 262 - Generated.soko1_2Potential.hole landing + bonus 262 (change p 262 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check782 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check783 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir288_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 .south p = true := by
  rfl
theorem dir288_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 .east p = true := by
  change ((!walkGuard soko1_2.board support p 288 289 .east || decide (bonus 288 p ≤ bonus 289 p)) && ((PreciseRolling.stayTargets soko1_2.board 289 .east).all (fun landing => !pushGuard support p 288 289 290 landing || decide (bonus 288 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 289 + bonus 289 (change p 289 (some landing)))) && (pushTargets soko1_2.board 289 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 288 289 290 landing || decide (bonus 288 p ≤ 1 - Generated.soko1_2Potential.boulder 289 - Generated.soko1_2Potential.hole landing + bonus 289 (change p 289 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check784 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check785 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir288_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 .west p = true := by
  rfl
theorem dir288_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 288 263 .northEast || decide (bonus 288 p ≤ bonus 263 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check786 p, rfl⟩
theorem dir288_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 .northWest p = true := by
  rfl
theorem dir288_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 .southEast p = true := by
  rfl
theorem dir288_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 288 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
