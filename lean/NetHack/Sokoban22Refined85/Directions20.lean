import NetHack.Sokoban22Refined85.Directions19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir245_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 .north p = true := by
  change ((!walkGuard soko2_2.board support p 245 223 .north || decide (bonus 245 p ≤ bonus 223 p)) && ((PreciseRolling.stayTargets soko2_2.board 223 .north).all (fun landing => !pushGuard support p 245 223 201 landing || decide (bonus 245 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 223 + bonus 223 (change p 223 (some landing)))) && (pushTargets soko2_2.board 223 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 245 223 201 landing || decide (bonus 245 p ≤ 1 - Generated.soko2_2Potential.boulder 223 - Generated.soko2_2Potential.hole landing + bonus 223 (change p 223 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check952 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check953 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir245_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 .south p = true := by
  rfl
theorem dir245_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 .east p = true := by
  change ((!walkGuard soko2_2.board support p 245 246 .east || decide (bonus 245 p ≤ bonus 246 p)) && ((PreciseRolling.stayTargets soko2_2.board 246 .east).all (fun landing => !pushGuard support p 245 246 247 landing || decide (bonus 245 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 246 + bonus 246 (change p 246 (some landing)))) && (pushTargets soko2_2.board 246 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 245 246 247 landing || decide (bonus 245 p ≤ 1 - Generated.soko2_2Potential.boulder 246 - Generated.soko2_2Potential.hole landing + bonus 246 (change p 246 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check954 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check955 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir245_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 .west p = true := by
  rfl
theorem dir245_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 245 224 .northEast || decide (bonus 245 p ≤ bonus 224 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check956 p, rfl⟩
theorem dir245_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 .northWest p = true := by
  rfl
theorem dir245_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 .southEast p = true := by
  rfl
theorem dir245_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 245 .southWest p = true := by
  rfl
theorem dir246_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 .north p = true := by
  change ((!walkGuard soko2_2.board support p 246 224 .north || decide (bonus 246 p ≤ bonus 224 p)) && ((PreciseRolling.stayTargets soko2_2.board 224 .north).all (fun landing => !pushGuard support p 246 224 202 landing || decide (bonus 246 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some landing)))) && (pushTargets soko2_2.board 224 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 246 224 202 landing || decide (bonus 246 p ≤ 1 - Generated.soko2_2Potential.boulder 224 - Generated.soko2_2Potential.hole landing + bonus 224 (change p 224 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check957 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check958 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir246_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 .south p = true := by
  rfl
theorem dir246_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 .east p = true := by
  change ((!walkGuard soko2_2.board support p 246 247 .east || decide (bonus 246 p ≤ bonus 247 p)) && ((PreciseRolling.stayTargets soko2_2.board 247 .east).all (fun landing => !pushGuard support p 246 247 248 landing || decide (bonus 246 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 247 + bonus 247 (change p 247 (some landing)))) && (pushTargets soko2_2.board 247 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 246 247 248 landing || decide (bonus 246 p ≤ 1 - Generated.soko2_2Potential.boulder 247 - Generated.soko2_2Potential.hole landing + bonus 247 (change p 247 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check959 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check960 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir246_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 .west p = true := by
  change ((!walkGuard soko2_2.board support p 246 245 .west || decide (bonus 246 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check961 p, rfl⟩
theorem dir246_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 246 225 .northEast || decide (bonus 246 p ≤ bonus 225 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check962 p, rfl⟩
theorem dir246_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 246 223 .northWest || decide (bonus 246 p ≤ bonus 223 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check963 p, rfl⟩
theorem dir246_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 .southEast p = true := by
  rfl
theorem dir246_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 246 .southWest p = true := by
  rfl
theorem dir247_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 .north p = true := by
  change ((!walkGuard soko2_2.board support p 247 225 .north || decide (bonus 247 p ≤ bonus 225 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check964 p, rfl⟩
theorem dir247_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 .south p = true := by
  rfl
theorem dir247_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 .east p = true := by
  change ((!walkGuard soko2_2.board support p 247 248 .east || decide (bonus 247 p ≤ bonus 248 p)) && ((PreciseRolling.stayTargets soko2_2.board 248 .east).all (fun landing => !pushGuard support p 247 248 249 landing || decide (bonus 247 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 248 + bonus 248 (change p 248 (some landing)))) && (pushTargets soko2_2.board 248 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 247 248 249 landing || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole landing + bonus 248 (change p 248 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check965 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (by intro cell member; cases member)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨check966 p, (List.forall_mem_cons.mpr ⟨check967 p, (List.forall_mem_cons.mpr ⟨check968 p, (List.forall_mem_cons.mpr ⟨check969 p, (List.forall_mem_cons.mpr ⟨check970 p, (List.forall_mem_cons.mpr ⟨check971 p, (List.forall_mem_cons.mpr ⟨check972 p, (List.forall_mem_cons.mpr ⟨check973 p, (List.forall_mem_cons.mpr ⟨check974 p, (List.forall_mem_cons.mpr ⟨check975 p, (List.forall_mem_cons.mpr ⟨check976 p, (by intro cell member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem dir247_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 .west p = true := by
  change ((!walkGuard soko2_2.board support p 247 246 .west || decide (bonus 247 p ≤ bonus 246 p)) && ((PreciseRolling.stayTargets soko2_2.board 246 .west).all (fun landing => !pushGuard support p 247 246 245 landing || decide (bonus 247 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 246 + bonus 246 (change p 246 (some landing)))) && (pushTargets soko2_2.board 246 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 247 246 245 landing || decide (bonus 247 p ≤ 1 - Generated.soko2_2Potential.boulder 246 - Generated.soko2_2Potential.hole landing + bonus 246 (change p 246 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check977 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check978 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir247_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 247 226 .northEast || decide (bonus 247 p ≤ bonus 226 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check979 p, rfl⟩
theorem dir247_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 247 224 .northWest || decide (bonus 247 p ≤ bonus 224 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check980 p, rfl⟩
theorem dir247_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 .southEast p = true := by
  rfl
theorem dir247_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 247 .southWest p = true := by
  rfl
theorem dir248_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 .north p = true := by
  change ((!walkGuard soko2_2.board support p 248 226 .north || decide (bonus 248 p ≤ bonus 226 p)) && ((PreciseRolling.stayTargets soko2_2.board 226 .north).all (fun landing => !pushGuard support p 248 226 204 landing || decide (bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 226 + bonus 226 (change p 226 (some landing)))) && (pushTargets soko2_2.board 226 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 248 226 204 landing || decide (bonus 248 p ≤ 1 - Generated.soko2_2Potential.boulder 226 - Generated.soko2_2Potential.hole landing + bonus 226 (change p 226 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check981 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check982 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir248_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 .south p = true := by
  rfl
theorem dir248_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 .east p = true := by
  change ((!walkGuard soko2_2.board support p 248 249 .east || decide (bonus 248 p ≤ bonus 249 p)) && ((PreciseRolling.stayTargets soko2_2.board 249 .east).all (fun landing => !pushGuard support p 248 249 250 landing || decide (bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 249 + bonus 249 (change p 249 (some landing)))) && (pushTargets soko2_2.board 249 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 248 249 250 landing || decide (bonus 248 p ≤ 1 - Generated.soko2_2Potential.boulder 249 - Generated.soko2_2Potential.hole landing + bonus 249 (change p 249 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check983 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check984 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check985 p, (by intro cell member; cases member)⟩)
theorem dir248_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 .west p = true := by
  change ((!walkGuard soko2_2.board support p 248 247 .west || decide (bonus 248 p ≤ bonus 247 p)) && ((PreciseRolling.stayTargets soko2_2.board 247 .west).all (fun landing => !pushGuard support p 248 247 246 landing || decide (bonus 248 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 247 + bonus 247 (change p 247 (some landing)))) && (pushTargets soko2_2.board 247 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 248 247 246 landing || decide (bonus 248 p ≤ 1 - Generated.soko2_2Potential.boulder 247 - Generated.soko2_2Potential.hole landing + bonus 247 (change p 247 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check986 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check987 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir248_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 .northEast p = true := by
  rfl
theorem dir248_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 248 225 .northWest || decide (bonus 248 p ≤ bonus 225 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check988 p, rfl⟩
theorem dir248_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 .southEast p = true := by
  rfl
theorem dir248_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 248 .southWest p = true := by
  rfl
theorem dir249_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 .north p = true := by
  rfl
theorem dir249_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 .south p = true := by
  rfl
theorem dir249_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 .east p = true := by
  change ((!walkGuard soko2_2.board support p 249 250 .east || decide (bonus 249 p ≤ bonus 250 p)) && ((PreciseRolling.stayTargets soko2_2.board 250 .east).all (fun landing => !pushGuard support p 249 250 251 landing || decide (bonus 249 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 250 + bonus 250 (change p 250 (some landing)))) && (pushTargets soko2_2.board 250 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 249 250 251 landing || decide (bonus 249 p ≤ 1 - Generated.soko2_2Potential.boulder 250 - Generated.soko2_2Potential.hole landing + bonus 250 (change p 250 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check989 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check990 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check991 p, (by intro cell member; cases member)⟩)
theorem dir249_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 .west p = true := by
  change ((!walkGuard soko2_2.board support p 249 248 .west || decide (bonus 249 p ≤ bonus 248 p)) && ((PreciseRolling.stayTargets soko2_2.board 248 .west).all (fun landing => !pushGuard support p 249 248 247 landing || decide (bonus 249 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 248 + bonus 248 (change p 248 (some landing)))) && (pushTargets soko2_2.board 248 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 249 248 247 landing || decide (bonus 249 p ≤ 1 - Generated.soko2_2Potential.boulder 248 - Generated.soko2_2Potential.hole landing + bonus 248 (change p 248 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check992 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check993 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir249_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 .northEast p = true := by
  rfl
theorem dir249_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 249 226 .northWest || decide (bonus 249 p ≤ bonus 226 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check994 p, rfl⟩
theorem dir249_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 .southEast p = true := by
  rfl
theorem dir249_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 249 .southWest p = true := by
  rfl
theorem dir250_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 .north p = true := by
  rfl
theorem dir250_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 .south p = true := by
  rfl
theorem dir250_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 .east p = true := by
  change ((!walkGuard soko2_2.board support p 250 251 .east || decide (bonus 250 p ≤ bonus 251 p)) && ((PreciseRolling.stayTargets soko2_2.board 251 .east).all (fun landing => !pushGuard support p 250 251 252 landing || decide (bonus 250 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 251 + bonus 251 (change p 251 (some landing)))) && (pushTargets soko2_2.board 251 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 250 251 252 landing || decide (bonus 250 p ≤ 1 - Generated.soko2_2Potential.boulder 251 - Generated.soko2_2Potential.hole landing + bonus 251 (change p 251 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check995 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check996 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check997 p, (by intro cell member; cases member)⟩)
theorem dir250_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 .west p = true := by
  change ((!walkGuard soko2_2.board support p 250 249 .west || decide (bonus 250 p ≤ bonus 249 p)) && ((PreciseRolling.stayTargets soko2_2.board 249 .west).all (fun landing => !pushGuard support p 250 249 248 landing || decide (bonus 250 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 249 + bonus 249 (change p 249 (some landing)))) && (pushTargets soko2_2.board 249 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 250 249 248 landing || decide (bonus 250 p ≤ 1 - Generated.soko2_2Potential.boulder 249 - Generated.soko2_2Potential.hole landing + bonus 249 (change p 249 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check998 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check999 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir250_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 .northEast p = true := by
  rfl
theorem dir250_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 .northWest p = true := by
  rfl
theorem dir250_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 .southEast p = true := by
  rfl
theorem dir250_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 250 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
