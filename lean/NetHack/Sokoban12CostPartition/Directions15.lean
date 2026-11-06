import NetHack.Sokoban12CostPartition.Directions14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir255_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 .north p = true := by
  rfl
theorem dir255_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 .south p = true := by
  change ((!walkGuard soko1_2.board support p 255 281 .south || decide (bonus 255 p ≤ bonus 281 p)) && ((PreciseRolling.stayTargets soko1_2.board 281 .south).all (fun landing => !pushGuard support p 255 281 307 landing || decide (bonus 255 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 281 + bonus 281 (change p 281 (some landing)))) && (pushTargets soko1_2.board 281 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 255 281 307 landing || decide (bonus 255 p ≤ 1 - Generated.soko1_2Potential.boulder 281 - Generated.soko1_2Potential.hole landing + bonus 281 (change p 281 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check659 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check660 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir255_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 .east p = true := by
  change ((!walkGuard soko1_2.board support p 255 256 .east || decide (bonus 255 p ≤ bonus 256 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check661 p, rfl⟩
theorem dir255_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 .west p = true := by
  change ((!walkGuard soko1_2.board support p 255 254 .west || decide (bonus 255 p ≤ bonus 254 p)) && ((PreciseRolling.stayTargets soko1_2.board 254 .west).all (fun landing => !pushGuard support p 255 254 253 landing || decide (bonus 255 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 254 + bonus 254 (change p 254 (some landing)))) && (pushTargets soko1_2.board 254 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 255 254 253 landing || decide (bonus 255 p ≤ 1 - Generated.soko1_2Potential.boulder 254 - Generated.soko1_2Potential.hole landing + bonus 254 (change p 254 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check662 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check663 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir255_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 .northEast p = true := by
  rfl
theorem dir255_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 .northWest p = true := by
  rfl
theorem dir255_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 255 282 .southEast || decide (bonus 255 p ≤ bonus 282 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check664 p, rfl⟩
theorem dir255_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 255 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 255 280 .southWest || decide (bonus 255 p ≤ bonus 280 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check665 p, rfl⟩
theorem dir256_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 .north p = true := by
  rfl
theorem dir256_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 .south p = true := by
  change ((!walkGuard soko1_2.board support p 256 282 .south || decide (bonus 256 p ≤ bonus 282 p)) && ((PreciseRolling.stayTargets soko1_2.board 282 .south).all (fun landing => !pushGuard support p 256 282 308 landing || decide (bonus 256 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 282 + bonus 282 (change p 282 (some landing)))) && (pushTargets soko1_2.board 282 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 256 282 308 landing || decide (bonus 256 p ≤ 1 - Generated.soko1_2Potential.boulder 282 - Generated.soko1_2Potential.hole landing + bonus 282 (change p 282 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check666 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check667 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir256_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 .east p = true := by
  rfl
theorem dir256_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 .west p = true := by
  change ((!walkGuard soko1_2.board support p 256 255 .west || decide (bonus 256 p ≤ bonus 255 p)) && ((PreciseRolling.stayTargets soko1_2.board 255 .west).all (fun landing => !pushGuard support p 256 255 254 landing || decide (bonus 256 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 255 + bonus 255 (change p 255 (some landing)))) && (pushTargets soko1_2.board 255 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 256 255 254 landing || decide (bonus 256 p ≤ 1 - Generated.soko1_2Potential.boulder 255 - Generated.soko1_2Potential.hole landing + bonus 255 (change p 255 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check668 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check669 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir256_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 .northEast p = true := by
  rfl
theorem dir256_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 .northWest p = true := by
  rfl
theorem dir256_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 .southEast p = true := by
  rfl
theorem dir256_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 256 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 256 281 .southWest || decide (bonus 256 p ≤ bonus 281 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check670 p, rfl⟩
theorem dir258_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 .north p = true := by
  change ((!walkGuard soko1_2.board support p 258 232 .north || decide (bonus 258 p ≤ bonus 232 p)) && ((PreciseRolling.stayTargets soko1_2.board 232 .north).all (fun landing => !pushGuard support p 258 232 206 landing || decide (bonus 258 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 232 + bonus 232 (change p 232 (some landing)))) && (pushTargets soko1_2.board 232 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 258 232 206 landing || decide (bonus 258 p ≤ 1 - Generated.soko1_2Potential.boulder 232 - Generated.soko1_2Potential.hole landing + bonus 232 (change p 232 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check671 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check672 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir258_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 .south p = true := by
  change ((!walkGuard soko1_2.board support p 258 284 .south || decide (bonus 258 p ≤ bonus 284 p)) && ((PreciseRolling.stayTargets soko1_2.board 284 .south).all (fun landing => !pushGuard support p 258 284 310 landing || decide (bonus 258 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 284 + bonus 284 (change p 284 (some landing)))) && (pushTargets soko1_2.board 284 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 258 284 310 landing || decide (bonus 258 p ≤ 1 - Generated.soko1_2Potential.boulder 284 - Generated.soko1_2Potential.hole landing + bonus 284 (change p 284 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check673 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check674 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir258_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 .east p = true := by
  rfl
theorem dir258_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 .west p = true := by
  rfl
theorem dir258_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 .northEast p = true := by
  rfl
theorem dir258_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 .northWest p = true := by
  rfl
theorem dir258_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 .southEast p = true := by
  rfl
theorem dir258_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 258 .southWest p = true := by
  rfl
theorem dir262_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 .north p = true := by
  change ((!walkGuard soko1_2.board support p 262 236 .north || decide (bonus 262 p ≤ bonus 236 p)) && ((PreciseRolling.stayTargets soko1_2.board 236 .north).all (fun landing => !pushGuard support p 262 236 210 landing || decide (bonus 262 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 236 + bonus 236 (change p 236 (some landing)))) && (pushTargets soko1_2.board 236 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 262 236 210 landing || decide (bonus 262 p ≤ 1 - Generated.soko1_2Potential.boulder 236 - Generated.soko1_2Potential.hole landing + bonus 236 (change p 236 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check675 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check676 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir262_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 .south p = true := by
  change ((!walkGuard soko1_2.board support p 262 288 .south || decide (bonus 262 p ≤ bonus 288 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check677 p, rfl⟩
theorem dir262_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 .east p = true := by
  change ((!walkGuard soko1_2.board support p 262 263 .east || decide (bonus 262 p ≤ bonus 263 p)) && ((PreciseRolling.stayTargets soko1_2.board 263 .east).all (fun landing => !pushGuard support p 262 263 264 landing || decide (bonus 262 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some landing)))) && (pushTargets soko1_2.board 263 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 262 263 264 landing || decide (bonus 262 p ≤ 1 - Generated.soko1_2Potential.boulder 263 - Generated.soko1_2Potential.hole landing + bonus 263 (change p 263 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check678 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check679 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir262_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 .west p = true := by
  rfl
theorem dir262_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 262 237 .northEast || decide (bonus 262 p ≤ bonus 237 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check680 p, rfl⟩
theorem dir262_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 .northWest p = true := by
  rfl
theorem dir262_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 262 289 .southEast || decide (bonus 262 p ≤ bonus 289 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check681 p, rfl⟩
theorem dir262_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 262 .southWest p = true := by
  rfl
theorem dir263_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 .north p = true := by
  change ((!walkGuard soko1_2.board support p 263 237 .north || decide (bonus 263 p ≤ bonus 237 p)) && ((PreciseRolling.stayTargets soko1_2.board 237 .north).all (fun landing => !pushGuard support p 263 237 211 landing || decide (bonus 263 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 237 + bonus 237 (change p 237 (some landing)))) && (pushTargets soko1_2.board 237 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 263 237 211 landing || decide (bonus 263 p ≤ 1 - Generated.soko1_2Potential.boulder 237 - Generated.soko1_2Potential.hole landing + bonus 237 (change p 237 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check682 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check683 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir263_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 .south p = true := by
  change ((!walkGuard soko1_2.board support p 263 289 .south || decide (bonus 263 p ≤ bonus 289 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check684 p, rfl⟩
theorem dir263_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 .east p = true := by
  change ((!walkGuard soko1_2.board support p 263 264 .east || decide (bonus 263 p ≤ bonus 264 p)) && ((PreciseRolling.stayTargets soko1_2.board 264 .east).all (fun landing => !pushGuard support p 263 264 265 landing || decide (bonus 263 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 264 + bonus 264 (change p 264 (some landing)))) && (pushTargets soko1_2.board 264 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 263 264 265 landing || decide (bonus 263 p ≤ 1 - Generated.soko1_2Potential.boulder 264 - Generated.soko1_2Potential.hole landing + bonus 264 (change p 264 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check685 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check686 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir263_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 .west p = true := by
  change ((!walkGuard soko1_2.board support p 263 262 .west || decide (bonus 263 p ≤ bonus 262 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check687 p, rfl⟩
theorem dir263_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 263 238 .northEast || decide (bonus 263 p ≤ bonus 238 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check688 p, rfl⟩
theorem dir263_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 263 236 .northWest || decide (bonus 263 p ≤ bonus 236 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check689 p, rfl⟩
theorem dir263_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 263 290 .southEast || decide (bonus 263 p ≤ bonus 290 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check690 p, rfl⟩
theorem dir263_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 263 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 263 288 .southWest || decide (bonus 263 p ≤ bonus 288 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check691 p, rfl⟩
theorem dir264_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 .north p = true := by
  change ((!walkGuard soko1_2.board support p 264 238 .north || decide (bonus 264 p ≤ bonus 238 p)) && ((PreciseRolling.stayTargets soko1_2.board 238 .north).all (fun landing => !pushGuard support p 264 238 212 landing || decide (bonus 264 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 238 + bonus 238 (change p 238 (some landing)))) && (pushTargets soko1_2.board 238 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 264 238 212 landing || decide (bonus 264 p ≤ 1 - Generated.soko1_2Potential.boulder 238 - Generated.soko1_2Potential.hole landing + bonus 238 (change p 238 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check692 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check693 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir264_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 .south p = true := by
  change ((!walkGuard soko1_2.board support p 264 290 .south || decide (bonus 264 p ≤ bonus 290 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check694 p, rfl⟩
theorem dir264_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 .east p = true := by
  change ((!walkGuard soko1_2.board support p 264 265 .east || decide (bonus 264 p ≤ bonus 265 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check695 p, rfl⟩
theorem dir264_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 .west p = true := by
  change ((!walkGuard soko1_2.board support p 264 263 .west || decide (bonus 264 p ≤ bonus 263 p)) && ((PreciseRolling.stayTargets soko1_2.board 263 .west).all (fun landing => !pushGuard support p 264 263 262 landing || decide (bonus 264 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 263 + bonus 263 (change p 263 (some landing)))) && (pushTargets soko1_2.board 263 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 264 263 262 landing || decide (bonus 264 p ≤ 1 - Generated.soko1_2Potential.boulder 263 - Generated.soko1_2Potential.hole landing + bonus 263 (change p 263 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check696 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check697 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir264_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 264 239 .northEast || decide (bonus 264 p ≤ bonus 239 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check698 p, rfl⟩
theorem dir264_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 264 237 .northWest || decide (bonus 264 p ≤ bonus 237 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check699 p, rfl⟩
theorem dir264_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 264 291 .southEast || decide (bonus 264 p ≤ bonus 291 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check700 p, rfl⟩
theorem dir264_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 264 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 264 289 .southWest || decide (bonus 264 p ≤ bonus 289 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check701 p, rfl⟩
end NetHack.Sokoban12CostPartition
