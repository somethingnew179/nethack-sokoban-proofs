import NetHack.Sokoban22Refined85.Directions21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir257_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 .north p = true := by
  rfl
theorem dir257_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 .south p = true := by
  rfl
theorem dir257_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 .east p = true := by
  change ((!walkGuard soko2_2.board support p 257 258 .east || decide (bonus 257 p ≤ bonus 258 p)) && ((PreciseRolling.stayTargets soko2_2.board 258 .east).all (fun landing => !pushGuard support p 257 258 259 landing || decide (bonus 257 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 258 + bonus 258 (change p 258 (some landing)))) && (pushTargets soko2_2.board 258 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 257 258 259 landing || decide (bonus 257 p ≤ 1 - Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.hole landing + bonus 258 (change p 258 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1036 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1037 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1038 p, (by intro cell member; cases member)⟩)
theorem dir257_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 .west p = true := by
  change ((!walkGuard soko2_2.board support p 257 256 .west || decide (bonus 257 p ≤ bonus 256 p)) && ((PreciseRolling.stayTargets soko2_2.board 256 .west).all (fun landing => !pushGuard support p 257 256 255 landing || decide (bonus 257 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 256 + bonus 256 (change p 256 (some landing)))) && (pushTargets soko2_2.board 256 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 257 256 255 landing || decide (bonus 257 p ≤ 1 - Generated.soko2_2Potential.boulder 256 - Generated.soko2_2Potential.hole landing + bonus 256 (change p 256 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1039 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1040 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1041 p, (by intro cell member; cases member)⟩)
theorem dir257_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 .northEast p = true := by
  rfl
theorem dir257_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 .northWest p = true := by
  rfl
theorem dir257_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 .southEast p = true := by
  rfl
theorem dir257_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 257 .southWest p = true := by
  rfl
theorem dir258_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 .north p = true := by
  rfl
theorem dir258_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 .south p = true := by
  rfl
theorem dir258_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 .east p = true := by
  change ((!walkGuard soko2_2.board support p 258 259 .east || decide (bonus 258 p ≤ bonus 259 p)) && ((PreciseRolling.stayTargets soko2_2.board 259 .east).all (fun landing => !pushGuard support p 258 259 260 landing || decide (bonus 258 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 259 + bonus 259 (change p 259 (some landing)))) && (pushTargets soko2_2.board 259 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 258 259 260 landing || decide (bonus 258 p ≤ 1 - Generated.soko2_2Potential.boulder 259 - Generated.soko2_2Potential.hole landing + bonus 259 (change p 259 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1042 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1043 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1044 p, (by intro cell member; cases member)⟩)
theorem dir258_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 .west p = true := by
  change ((!walkGuard soko2_2.board support p 258 257 .west || decide (bonus 258 p ≤ bonus 257 p)) && ((PreciseRolling.stayTargets soko2_2.board 257 .west).all (fun landing => !pushGuard support p 258 257 256 landing || decide (bonus 258 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 257 + bonus 257 (change p 257 (some landing)))) && (pushTargets soko2_2.board 257 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 258 257 256 landing || decide (bonus 258 p ≤ 1 - Generated.soko2_2Potential.boulder 257 - Generated.soko2_2Potential.hole landing + bonus 257 (change p 257 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1045 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1046 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1047 p, (by intro cell member; cases member)⟩)
theorem dir258_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 .northEast p = true := by
  rfl
theorem dir258_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 .northWest p = true := by
  rfl
theorem dir258_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 .southEast p = true := by
  rfl
theorem dir258_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 258 .southWest p = true := by
  rfl
theorem dir259_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 .north p = true := by
  rfl
theorem dir259_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 .south p = true := by
  rfl
theorem dir259_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 .east p = true := by
  change ((!walkGuard soko2_2.board support p 259 260 .east || decide (bonus 259 p ≤ bonus 260 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1048 p, rfl⟩
theorem dir259_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 .west p = true := by
  change ((!walkGuard soko2_2.board support p 259 258 .west || decide (bonus 259 p ≤ bonus 258 p)) && ((PreciseRolling.stayTargets soko2_2.board 258 .west).all (fun landing => !pushGuard support p 259 258 257 landing || decide (bonus 259 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 258 + bonus 258 (change p 258 (some landing)))) && (pushTargets soko2_2.board 258 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 259 258 257 landing || decide (bonus 259 p ≤ 1 - Generated.soko2_2Potential.boulder 258 - Generated.soko2_2Potential.hole landing + bonus 258 (change p 258 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1049 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1050 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1051 p, (by intro cell member; cases member)⟩)
theorem dir259_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 .northEast p = true := by
  rfl
theorem dir259_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 .northWest p = true := by
  rfl
theorem dir259_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 .southEast p = true := by
  rfl
theorem dir259_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 259 .southWest p = true := by
  rfl
theorem dir260_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 .north p = true := by
  rfl
theorem dir260_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 .south p = true := by
  rfl
theorem dir260_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 .east p = true := by
  rfl
theorem dir260_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 .west p = true := by
  change ((!walkGuard soko2_2.board support p 260 259 .west || decide (bonus 260 p ≤ bonus 259 p)) && ((PreciseRolling.stayTargets soko2_2.board 259 .west).all (fun landing => !pushGuard support p 260 259 258 landing || decide (bonus 260 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 259 + bonus 259 (change p 259 (some landing)))) && (pushTargets soko2_2.board 259 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 260 259 258 landing || decide (bonus 260 p ≤ 1 - Generated.soko2_2Potential.boulder 259 - Generated.soko2_2Potential.hole landing + bonus 259 (change p 259 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1052 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1053 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1054 p, (by intro cell member; cases member)⟩)
theorem dir260_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 .northEast p = true := by
  rfl
theorem dir260_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 .northWest p = true := by
  rfl
theorem dir260_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 .southEast p = true := by
  rfl
theorem dir260_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 260 .southWest p = true := by
  rfl
theorem dir262_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 .north p = true := by
  change ((!walkGuard soko2_2.board support p 262 240 .north || decide (bonus 262 p ≤ bonus 240 p)) && ((PreciseRolling.stayTargets soko2_2.board 240 .north).all (fun landing => !pushGuard support p 262 240 218 landing || decide (bonus 262 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 240 + bonus 240 (change p 240 (some landing)))) && (pushTargets soko2_2.board 240 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 262 240 218 landing || decide (bonus 262 p ≤ 1 - Generated.soko2_2Potential.boulder 240 - Generated.soko2_2Potential.hole landing + bonus 240 (change p 240 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1055 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1056 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir262_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 .south p = true := by
  rfl
theorem dir262_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 .east p = true := by
  rfl
theorem dir262_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 .west p = true := by
  rfl
theorem dir262_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 .northEast p = true := by
  rfl
theorem dir262_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 .northWest p = true := by
  rfl
theorem dir262_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 .southEast p = true := by
  rfl
theorem dir262_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 262 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
