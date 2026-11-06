import NetHack.Sokoban32Refined.Directions19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir226_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 .north p = true := by
  change ((!walkGuard soko3_2.board support p 226 200 .north || decide (bonus 226 p ≤ bonus 200 p)) && ((PreciseRolling.stayTargets soko3_2.board 200 .north).all (fun landing => !pushGuard support p 226 200 174 landing || decide (bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some landing)))) && (pushTargets soko3_2.board 200 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 226 200 174 landing || decide (bonus 226 p ≤ 1 - Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.hole landing + bonus 200 (change p 200 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1013 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1014 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir226_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 .south p = true := by
  rfl
theorem dir226_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 .east p = true := by
  change ((!walkGuard soko3_2.board support p 226 227 .east || decide (bonus 226 p ≤ bonus 227 p)) && ((PreciseRolling.stayTargets soko3_2.board 227 .east).all (fun landing => !pushGuard support p 226 227 228 landing || decide (bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 227 + bonus 227 (change p 227 (some landing)))) && (pushTargets soko3_2.board 227 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 226 227 228 landing || decide (bonus 226 p ≤ 1 - Generated.soko3_2Potential.boulder 227 - Generated.soko3_2Potential.hole landing + bonus 227 (change p 227 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1015 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1016 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir226_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 .west p = true := by
  change ((!walkGuard soko3_2.board support p 226 225 .west || decide (bonus 226 p ≤ bonus 225 p)) && ((PreciseRolling.stayTargets soko3_2.board 225 .west).all (fun landing => !pushGuard support p 226 225 224 landing || decide (bonus 226 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 225 + bonus 225 (change p 225 (some landing)))) && (pushTargets soko3_2.board 225 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 226 225 224 landing || decide (bonus 226 p ≤ 1 - Generated.soko3_2Potential.boulder 225 - Generated.soko3_2Potential.hole landing + bonus 225 (change p 225 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1017 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1018 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir226_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 226 201 .northEast || decide (bonus 226 p ≤ bonus 201 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1019 p, rfl⟩
theorem dir226_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 226 199 .northWest || decide (bonus 226 p ≤ bonus 199 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1020 p, rfl⟩
theorem dir226_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 .southEast p = true := by
  rfl
theorem dir226_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 226 .southWest p = true := by
  rfl
theorem dir227_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 .north p = true := by
  change ((!walkGuard soko3_2.board support p 227 201 .north || decide (bonus 227 p ≤ bonus 201 p)) && ((PreciseRolling.stayTargets soko3_2.board 201 .north).all (fun landing => !pushGuard support p 227 201 175 landing || decide (bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some landing)))) && (pushTargets soko3_2.board 201 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 227 201 175 landing || decide (bonus 227 p ≤ 1 - Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.hole landing + bonus 201 (change p 201 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1021 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1022 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir227_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 .south p = true := by
  rfl
theorem dir227_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 .east p = true := by
  change ((!walkGuard soko3_2.board support p 227 228 .east || decide (bonus 227 p ≤ bonus 228 p)) && ((PreciseRolling.stayTargets soko3_2.board 228 .east).all (fun landing => !pushGuard support p 227 228 229 landing || decide (bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 228 + bonus 228 (change p 228 (some landing)))) && (pushTargets soko3_2.board 228 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 227 228 229 landing || decide (bonus 227 p ≤ 1 - Generated.soko3_2Potential.boulder 228 - Generated.soko3_2Potential.hole landing + bonus 228 (change p 228 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1023 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1024 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir227_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 .west p = true := by
  change ((!walkGuard soko3_2.board support p 227 226 .west || decide (bonus 227 p ≤ bonus 226 p)) && ((PreciseRolling.stayTargets soko3_2.board 226 .west).all (fun landing => !pushGuard support p 227 226 225 landing || decide (bonus 227 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 226 + bonus 226 (change p 226 (some landing)))) && (pushTargets soko3_2.board 226 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 227 226 225 landing || decide (bonus 227 p ≤ 1 - Generated.soko3_2Potential.boulder 226 - Generated.soko3_2Potential.hole landing + bonus 226 (change p 226 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1025 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1026 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir227_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 227 202 .northEast || decide (bonus 227 p ≤ bonus 202 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1027 p, rfl⟩
theorem dir227_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 227 200 .northWest || decide (bonus 227 p ≤ bonus 200 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1028 p, rfl⟩
theorem dir227_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 .southEast p = true := by
  rfl
theorem dir227_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 227 .southWest p = true := by
  rfl
theorem dir228_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 .north p = true := by
  change ((!walkGuard soko3_2.board support p 228 202 .north || decide (bonus 228 p ≤ bonus 202 p)) && ((PreciseRolling.stayTargets soko3_2.board 202 .north).all (fun landing => !pushGuard support p 228 202 176 landing || decide (bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some landing)))) && (pushTargets soko3_2.board 202 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 228 202 176 landing || decide (bonus 228 p ≤ 1 - Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.hole landing + bonus 202 (change p 202 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1029 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1030 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir228_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 .south p = true := by
  rfl
theorem dir228_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 .east p = true := by
  change ((!walkGuard soko3_2.board support p 228 229 .east || decide (bonus 228 p ≤ bonus 229 p)) && ((PreciseRolling.stayTargets soko3_2.board 229 .east).all (fun landing => !pushGuard support p 228 229 230 landing || decide (bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 229 + bonus 229 (change p 229 (some landing)))) && (pushTargets soko3_2.board 229 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 228 229 230 landing || decide (bonus 228 p ≤ 1 - Generated.soko3_2Potential.boulder 229 - Generated.soko3_2Potential.hole landing + bonus 229 (change p 229 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1031 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1032 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir228_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 .west p = true := by
  change ((!walkGuard soko3_2.board support p 228 227 .west || decide (bonus 228 p ≤ bonus 227 p)) && ((PreciseRolling.stayTargets soko3_2.board 227 .west).all (fun landing => !pushGuard support p 228 227 226 landing || decide (bonus 228 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 227 + bonus 227 (change p 227 (some landing)))) && (pushTargets soko3_2.board 227 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 228 227 226 landing || decide (bonus 228 p ≤ 1 - Generated.soko3_2Potential.boulder 227 - Generated.soko3_2Potential.hole landing + bonus 227 (change p 227 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1033 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1034 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir228_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 228 203 .northEast || decide (bonus 228 p ≤ bonus 203 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1035 p, rfl⟩
theorem dir228_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 228 201 .northWest || decide (bonus 228 p ≤ bonus 201 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1036 p, rfl⟩
theorem dir228_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 .southEast p = true := by
  rfl
theorem dir228_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 228 .southWest p = true := by
  rfl
theorem dir229_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 .north p = true := by
  change ((!walkGuard soko3_2.board support p 229 203 .north || decide (bonus 229 p ≤ bonus 203 p)) && ((PreciseRolling.stayTargets soko3_2.board 203 .north).all (fun landing => !pushGuard support p 229 203 177 landing || decide (bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some landing)))) && (pushTargets soko3_2.board 203 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 229 203 177 landing || decide (bonus 229 p ≤ 1 - Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.hole landing + bonus 203 (change p 203 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1037 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1038 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir229_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 .south p = true := by
  rfl
theorem dir229_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 .east p = true := by
  change ((!walkGuard soko3_2.board support p 229 230 .east || decide (bonus 229 p ≤ bonus 230 p)) && ((PreciseRolling.stayTargets soko3_2.board 230 .east).all (fun landing => !pushGuard support p 229 230 231 landing || decide (bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 230 + bonus 230 (change p 230 (some landing)))) && (pushTargets soko3_2.board 230 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 229 230 231 landing || decide (bonus 229 p ≤ 1 - Generated.soko3_2Potential.boulder 230 - Generated.soko3_2Potential.hole landing + bonus 230 (change p 230 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1039 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1040 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir229_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 .west p = true := by
  change ((!walkGuard soko3_2.board support p 229 228 .west || decide (bonus 229 p ≤ bonus 228 p)) && ((PreciseRolling.stayTargets soko3_2.board 228 .west).all (fun landing => !pushGuard support p 229 228 227 landing || decide (bonus 229 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 228 + bonus 228 (change p 228 (some landing)))) && (pushTargets soko3_2.board 228 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 229 228 227 landing || decide (bonus 229 p ≤ 1 - Generated.soko3_2Potential.boulder 228 - Generated.soko3_2Potential.hole landing + bonus 228 (change p 228 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1041 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1042 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir229_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 229 204 .northEast || decide (bonus 229 p ≤ bonus 204 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1043 p, rfl⟩
theorem dir229_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 229 202 .northWest || decide (bonus 229 p ≤ bonus 202 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1044 p, rfl⟩
theorem dir229_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 .southEast p = true := by
  rfl
theorem dir229_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 229 .southWest p = true := by
  rfl
theorem dir230_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 .north p = true := by
  change ((!walkGuard soko3_2.board support p 230 204 .north || decide (bonus 230 p ≤ bonus 204 p)) && ((PreciseRolling.stayTargets soko3_2.board 204 .north).all (fun landing => !pushGuard support p 230 204 178 landing || decide (bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some landing)))) && (pushTargets soko3_2.board 204 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 230 204 178 landing || decide (bonus 230 p ≤ 1 - Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.hole landing + bonus 204 (change p 204 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1045 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1046 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir230_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 .south p = true := by
  rfl
theorem dir230_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 .east p = true := by
  change ((!walkGuard soko3_2.board support p 230 231 .east || decide (bonus 230 p ≤ bonus 231 p)) && ((PreciseRolling.stayTargets soko3_2.board 231 .east).all (fun landing => !pushGuard support p 230 231 232 landing || decide (bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 231 + bonus 231 (change p 231 (some landing)))) && (pushTargets soko3_2.board 231 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 230 231 232 landing || decide (bonus 230 p ≤ 1 - Generated.soko3_2Potential.boulder 231 - Generated.soko3_2Potential.hole landing + bonus 231 (change p 231 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1047 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1048 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir230_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 .west p = true := by
  change ((!walkGuard soko3_2.board support p 230 229 .west || decide (bonus 230 p ≤ bonus 229 p)) && ((PreciseRolling.stayTargets soko3_2.board 229 .west).all (fun landing => !pushGuard support p 230 229 228 landing || decide (bonus 230 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 229 + bonus 229 (change p 229 (some landing)))) && (pushTargets soko3_2.board 229 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 230 229 228 landing || decide (bonus 230 p ≤ 1 - Generated.soko3_2Potential.boulder 229 - Generated.soko3_2Potential.hole landing + bonus 229 (change p 229 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1049 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1050 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir230_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 230 205 .northEast || decide (bonus 230 p ≤ bonus 205 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1051 p, rfl⟩
theorem dir230_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 230 203 .northWest || decide (bonus 230 p ≤ bonus 203 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1052 p, rfl⟩
theorem dir230_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 .southEast p = true := by
  rfl
theorem dir230_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 230 .southWest p = true := by
  rfl
theorem dir231_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 .north p = true := by
  change ((!walkGuard soko3_2.board support p 231 205 .north || decide (bonus 231 p ≤ bonus 205 p)) && ((PreciseRolling.stayTargets soko3_2.board 205 .north).all (fun landing => !pushGuard support p 231 205 179 landing || decide (bonus 231 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some landing)))) && (pushTargets soko3_2.board 205 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 231 205 179 landing || decide (bonus 231 p ≤ 1 - Generated.soko3_2Potential.boulder 205 - Generated.soko3_2Potential.hole landing + bonus 205 (change p 205 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1053 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1054 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir231_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 .south p = true := by
  rfl
theorem dir231_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 .east p = true := by
  change ((!walkGuard soko3_2.board support p 231 232 .east || decide (bonus 231 p ≤ bonus 232 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1055 p, rfl⟩
theorem dir231_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 .west p = true := by
  change ((!walkGuard soko3_2.board support p 231 230 .west || decide (bonus 231 p ≤ bonus 230 p)) && ((PreciseRolling.stayTargets soko3_2.board 230 .west).all (fun landing => !pushGuard support p 231 230 229 landing || decide (bonus 231 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 230 + bonus 230 (change p 230 (some landing)))) && (pushTargets soko3_2.board 230 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 231 230 229 landing || decide (bonus 231 p ≤ 1 - Generated.soko3_2Potential.boulder 230 - Generated.soko3_2Potential.hole landing + bonus 230 (change p 230 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1056 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1057 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir231_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 231 206 .northEast || decide (bonus 231 p ≤ bonus 206 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1058 p, rfl⟩
theorem dir231_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 231 204 .northWest || decide (bonus 231 p ≤ bonus 204 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1059 p, rfl⟩
theorem dir231_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 .southEast p = true := by
  rfl
theorem dir231_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 231 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
