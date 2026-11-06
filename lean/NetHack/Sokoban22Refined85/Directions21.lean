import NetHack.Sokoban22Refined85.Directions20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir251_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 .north p = true := by
  rfl
theorem dir251_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 .south p = true := by
  rfl
theorem dir251_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 .east p = true := by
  change ((!walkGuard soko2_2.board support p 251 252 .east || decide (bonus 251 p ≤ bonus 252 p)) && ((PreciseRolling.stayTargets soko2_2.board 252 .east).all (fun landing => !pushGuard support p 251 252 253 landing || decide (bonus 251 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 252 + bonus 252 (change p 252 (some landing)))) && (pushTargets soko2_2.board 252 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 251 252 253 landing || decide (bonus 251 p ≤ 1 - Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.hole landing + bonus 252 (change p 252 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1000 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1001 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1002 p, (by intro cell member; cases member)⟩)
theorem dir251_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 .west p = true := by
  change ((!walkGuard soko2_2.board support p 251 250 .west || decide (bonus 251 p ≤ bonus 250 p)) && ((PreciseRolling.stayTargets soko2_2.board 250 .west).all (fun landing => !pushGuard support p 251 250 249 landing || decide (bonus 251 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 250 + bonus 250 (change p 250 (some landing)))) && (pushTargets soko2_2.board 250 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 251 250 249 landing || decide (bonus 251 p ≤ 1 - Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.hole landing + bonus 250 (change p 250 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1003 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1004 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1005 p, (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)
theorem dir251_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 .northEast p = true := by
  rfl
theorem dir251_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 .northWest p = true := by
  rfl
theorem dir251_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 .southEast p = true := by
  rfl
theorem dir251_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 251 .southWest p = true := by
  rfl
theorem dir252_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 .north p = true := by
  rfl
theorem dir252_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 .south p = true := by
  rfl
theorem dir252_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 .east p = true := by
  change ((!walkGuard soko2_2.board support p 252 253 .east || decide (bonus 252 p ≤ bonus 253 p)) && ((PreciseRolling.stayTargets soko2_2.board 253 .east).all (fun landing => !pushGuard support p 252 253 254 landing || decide (bonus 252 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 253 + bonus 253 (change p 253 (some landing)))) && (pushTargets soko2_2.board 253 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 252 253 254 landing || decide (bonus 252 p ≤ 1 - Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.hole landing + bonus 253 (change p 253 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1006 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1007 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1008 p, (by intro cell member; cases member)⟩)
theorem dir252_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 .west p = true := by
  change ((!walkGuard soko2_2.board support p 252 251 .west || decide (bonus 252 p ≤ bonus 251 p)) && ((PreciseRolling.stayTargets soko2_2.board 251 .west).all (fun landing => !pushGuard support p 252 251 250 landing || decide (bonus 252 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 251 + bonus 251 (change p 251 (some landing)))) && (pushTargets soko2_2.board 251 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 252 251 250 landing || decide (bonus 252 p ≤ 1 - Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.hole landing + bonus 251 (change p 251 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1009 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1010 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1011 p, (by intro cell member; cases member)⟩)
theorem dir252_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 .northEast p = true := by
  rfl
theorem dir252_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 .northWest p = true := by
  rfl
theorem dir252_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 .southEast p = true := by
  rfl
theorem dir252_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 252 .southWest p = true := by
  rfl
theorem dir253_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 .north p = true := by
  rfl
theorem dir253_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 .south p = true := by
  rfl
theorem dir253_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 .east p = true := by
  change ((!walkGuard soko2_2.board support p 253 254 .east || decide (bonus 253 p ≤ bonus 254 p)) && ((PreciseRolling.stayTargets soko2_2.board 254 .east).all (fun landing => !pushGuard support p 253 254 255 landing || decide (bonus 253 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 254 + bonus 254 (change p 254 (some landing)))) && (pushTargets soko2_2.board 254 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 253 254 255 landing || decide (bonus 253 p ≤ 1 - Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.hole landing + bonus 254 (change p 254 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1012 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1013 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1014 p, (by intro cell member; cases member)⟩)
theorem dir253_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 .west p = true := by
  change ((!walkGuard soko2_2.board support p 253 252 .west || decide (bonus 253 p ≤ bonus 252 p)) && ((PreciseRolling.stayTargets soko2_2.board 252 .west).all (fun landing => !pushGuard support p 253 252 251 landing || decide (bonus 253 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 252 + bonus 252 (change p 252 (some landing)))) && (pushTargets soko2_2.board 252 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 253 252 251 landing || decide (bonus 253 p ≤ 1 - Generated.soko2_2Potential.boulder 252 - Generated.soko2_2Potential.hole landing + bonus 252 (change p 252 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1015 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1016 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1017 p, (by intro cell member; cases member)⟩)
theorem dir253_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 .northEast p = true := by
  rfl
theorem dir253_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 .northWest p = true := by
  rfl
theorem dir253_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 .southEast p = true := by
  rfl
theorem dir253_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 253 .southWest p = true := by
  rfl
theorem dir254_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 .north p = true := by
  rfl
theorem dir254_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 .south p = true := by
  rfl
theorem dir254_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 .east p = true := by
  change ((!walkGuard soko2_2.board support p 254 255 .east || decide (bonus 254 p ≤ bonus 255 p)) && ((PreciseRolling.stayTargets soko2_2.board 255 .east).all (fun landing => !pushGuard support p 254 255 256 landing || decide (bonus 254 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 255 + bonus 255 (change p 255 (some landing)))) && (pushTargets soko2_2.board 255 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 254 255 256 landing || decide (bonus 254 p ≤ 1 - Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.hole landing + bonus 255 (change p 255 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1018 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1019 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1020 p, (by intro cell member; cases member)⟩)
theorem dir254_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 .west p = true := by
  change ((!walkGuard soko2_2.board support p 254 253 .west || decide (bonus 254 p ≤ bonus 253 p)) && ((PreciseRolling.stayTargets soko2_2.board 253 .west).all (fun landing => !pushGuard support p 254 253 252 landing || decide (bonus 254 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 253 + bonus 253 (change p 253 (some landing)))) && (pushTargets soko2_2.board 253 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 254 253 252 landing || decide (bonus 254 p ≤ 1 - Generated.soko2_2Potential.boulder 253 - Generated.soko2_2Potential.hole landing + bonus 253 (change p 253 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1021 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1022 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1023 p, (by intro cell member; cases member)⟩)
theorem dir254_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 .northEast p = true := by
  rfl
theorem dir254_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 .northWest p = true := by
  rfl
theorem dir254_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 .southEast p = true := by
  rfl
theorem dir254_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 254 .southWest p = true := by
  rfl
theorem dir255_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 .north p = true := by
  rfl
theorem dir255_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 .south p = true := by
  rfl
theorem dir255_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 .east p = true := by
  change ((!walkGuard soko2_2.board support p 255 256 .east || decide (bonus 255 p ≤ bonus 256 p)) && ((PreciseRolling.stayTargets soko2_2.board 256 .east).all (fun landing => !pushGuard support p 255 256 257 landing || decide (bonus 255 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 256 + bonus 256 (change p 256 (some landing)))) && (pushTargets soko2_2.board 256 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 255 256 257 landing || decide (bonus 255 p ≤ 1 - Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.hole landing + bonus 256 (change p 256 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1024 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1025 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1026 p, (by intro cell member; cases member)⟩)
theorem dir255_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 .west p = true := by
  change ((!walkGuard soko2_2.board support p 255 254 .west || decide (bonus 255 p ≤ bonus 254 p)) && ((PreciseRolling.stayTargets soko2_2.board 254 .west).all (fun landing => !pushGuard support p 255 254 253 landing || decide (bonus 255 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 254 + bonus 254 (change p 254 (some landing)))) && (pushTargets soko2_2.board 254 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 255 254 253 landing || decide (bonus 255 p ≤ 1 - Generated.soko2_2Potential.boulder 254 - Generated.soko2_2Potential.hole landing + bonus 254 (change p 254 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1027 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1028 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1029 p, (by intro cell member; cases member)⟩)
theorem dir255_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 .northEast p = true := by
  rfl
theorem dir255_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 .northWest p = true := by
  rfl
theorem dir255_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 .southEast p = true := by
  rfl
theorem dir255_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 255 .southWest p = true := by
  rfl
theorem dir256_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 .north p = true := by
  rfl
theorem dir256_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 .south p = true := by
  rfl
theorem dir256_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 .east p = true := by
  change ((!walkGuard soko2_2.board support p 256 257 .east || decide (bonus 256 p ≤ bonus 257 p)) && ((PreciseRolling.stayTargets soko2_2.board 257 .east).all (fun landing => !pushGuard support p 256 257 258 landing || decide (bonus 256 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 257 + bonus 257 (change p 257 (some landing)))) && (pushTargets soko2_2.board 257 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 256 257 258 landing || decide (bonus 256 p ≤ 1 - Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.hole landing + bonus 257 (change p 257 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1030 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1031 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1032 p, (by intro cell member; cases member)⟩)
theorem dir256_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 .west p = true := by
  change ((!walkGuard soko2_2.board support p 256 255 .west || decide (bonus 256 p ≤ bonus 255 p)) && ((PreciseRolling.stayTargets soko2_2.board 255 .west).all (fun landing => !pushGuard support p 256 255 254 landing || decide (bonus 256 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 255 + bonus 255 (change p 255 (some landing)))) && (pushTargets soko2_2.board 255 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 256 255 254 landing || decide (bonus 256 p ≤ 1 - Generated.soko2_2Potential.boulder 255 - Generated.soko2_2Potential.hole landing + bonus 255 (change p 255 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1033 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1034 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1035 p, (by intro cell member; cases member)⟩)
theorem dir256_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 .northEast p = true := by
  rfl
theorem dir256_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 .northWest p = true := by
  rfl
theorem dir256_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 .southEast p = true := by
  rfl
theorem dir256_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 256 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
