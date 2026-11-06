import NetHack.Sokoban32Refined.Directions18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir214_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 .north p = true := by
  change ((!walkGuard soko3_2.board support p 214 188 .north || decide (bonus 214 p ≤ bonus 188 p)) && ((PreciseRolling.stayTargets soko3_2.board 188 .north).all (fun landing => !pushGuard support p 214 188 162 landing || decide (bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 188 + bonus 188 (change p 188 (some landing)))) && (pushTargets soko3_2.board 188 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 214 188 162 landing || decide (bonus 214 p ≤ 1 - Generated.soko3_2Potential.boulder 188 - Generated.soko3_2Potential.hole landing + bonus 188 (change p 188 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check971 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check972 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir214_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 .south p = true := by
  rfl
theorem dir214_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 .east p = true := by
  change ((!walkGuard soko3_2.board support p 214 215 .east || decide (bonus 214 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko3_2.board 215 .east).all (fun landing => !pushGuard support p 214 215 216 landing || decide (bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko3_2.board 215 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 214 215 216 landing || decide (bonus 214 p ≤ 1 - Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check973 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check974 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir214_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 .west p = true := by
  change ((!walkGuard soko3_2.board support p 214 213 .west || decide (bonus 214 p ≤ bonus 213 p)) && ((PreciseRolling.stayTargets soko3_2.board 213 .west).all (fun landing => !pushGuard support p 214 213 212 landing || decide (bonus 214 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 213 + bonus 213 (change p 213 (some landing)))) && (pushTargets soko3_2.board 213 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 214 213 212 landing || decide (bonus 214 p ≤ 1 - Generated.soko3_2Potential.boulder 213 - Generated.soko3_2Potential.hole landing + bonus 213 (change p 213 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check975 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check976 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir214_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 214 189 .northEast || decide (bonus 214 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check977 p, rfl⟩
theorem dir214_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 .northWest p = true := by
  rfl
theorem dir214_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 214 241 .southEast || decide (bonus 214 p ≤ bonus 241 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check978 p, rfl⟩
theorem dir214_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 214 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 214 239 .southWest || decide (bonus 214 p ≤ bonus 239 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check979 p, rfl⟩
theorem dir215_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 .north p = true := by
  change ((!walkGuard soko3_2.board support p 215 189 .north || decide (bonus 215 p ≤ bonus 189 p)) && ((PreciseRolling.stayTargets soko3_2.board 189 .north).all (fun landing => !pushGuard support p 215 189 163 landing || decide (bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 189 + bonus 189 (change p 189 (some landing)))) && (pushTargets soko3_2.board 189 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 215 189 163 landing || decide (bonus 215 p ≤ 1 - Generated.soko3_2Potential.boulder 189 - Generated.soko3_2Potential.hole landing + bonus 189 (change p 189 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check980 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check981 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir215_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 .south p = true := by
  change ((!walkGuard soko3_2.board support p 215 241 .south || decide (bonus 215 p ≤ bonus 241 p)) && ((PreciseRolling.stayTargets soko3_2.board 241 .south).all (fun landing => !pushGuard support p 215 241 267 landing || decide (bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 241 + bonus 241 (change p 241 (some landing)))) && (pushTargets soko3_2.board 241 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 215 241 267 landing || decide (bonus 215 p ≤ 1 - Generated.soko3_2Potential.boulder 241 - Generated.soko3_2Potential.hole landing + bonus 241 (change p 241 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check982 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check983 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir215_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 .east p = true := by
  change ((!walkGuard soko3_2.board support p 215 216 .east || decide (bonus 215 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check984 p, rfl⟩
theorem dir215_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 .west p = true := by
  change ((!walkGuard soko3_2.board support p 215 214 .west || decide (bonus 215 p ≤ bonus 214 p)) && ((PreciseRolling.stayTargets soko3_2.board 214 .west).all (fun landing => !pushGuard support p 215 214 213 landing || decide (bonus 215 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 214 + bonus 214 (change p 214 (some landing)))) && (pushTargets soko3_2.board 214 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 215 214 213 landing || decide (bonus 215 p ≤ 1 - Generated.soko3_2Potential.boulder 214 - Generated.soko3_2Potential.hole landing + bonus 214 (change p 214 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check985 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check986 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir215_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 .northEast p = true := by
  rfl
theorem dir215_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 215 188 .northWest || decide (bonus 215 p ≤ bonus 188 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check987 p, rfl⟩
theorem dir215_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 215 242 .southEast || decide (bonus 215 p ≤ bonus 242 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check988 p, rfl⟩
theorem dir215_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 215 .southWest p = true := by
  rfl
theorem dir216_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 .north p = true := by
  rfl
theorem dir216_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 .south p = true := by
  change ((!walkGuard soko3_2.board support p 216 242 .south || decide (bonus 216 p ≤ bonus 242 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check989 p, rfl⟩
theorem dir216_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 .east p = true := by
  rfl
theorem dir216_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 .west p = true := by
  change ((!walkGuard soko3_2.board support p 216 215 .west || decide (bonus 216 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko3_2.board 215 .west).all (fun landing => !pushGuard support p 216 215 214 landing || decide (bonus 216 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko3_2.board 215 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 216 215 214 landing || decide (bonus 216 p ≤ 1 - Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check990 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check991 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir216_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 .northEast p = true := by
  rfl
theorem dir216_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 216 189 .northWest || decide (bonus 216 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check992 p, rfl⟩
theorem dir216_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 216 243 .southEast || decide (bonus 216 p ≤ bonus 243 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check993 p, rfl⟩
theorem dir216_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 216 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 216 241 .southWest || decide (bonus 216 p ≤ bonus 241 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check994 p, rfl⟩
theorem dir218_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 .north p = true := by
  change ((!walkGuard soko3_2.board support p 218 192 .north || decide (bonus 218 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko3_2.board 192 .north).all (fun landing => !pushGuard support p 218 192 166 landing || decide (bonus 218 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko3_2.board 192 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 218 192 166 landing || decide (bonus 218 p ≤ 1 - Generated.soko3_2Potential.boulder 192 - Generated.soko3_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check995 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check996 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir218_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 .south p = true := by
  change ((!walkGuard soko3_2.board support p 218 244 .south || decide (bonus 218 p ≤ bonus 244 p)) && ((PreciseRolling.stayTargets soko3_2.board 244 .south).all (fun landing => !pushGuard support p 218 244 270 landing || decide (bonus 218 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some landing)))) && (pushTargets soko3_2.board 244 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 218 244 270 landing || decide (bonus 218 p ≤ 1 - Generated.soko3_2Potential.boulder 244 - Generated.soko3_2Potential.hole landing + bonus 244 (change p 244 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check997 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check998 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir218_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 .east p = true := by
  rfl
theorem dir218_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 .west p = true := by
  rfl
theorem dir218_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 .northEast p = true := by
  rfl
theorem dir218_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 .northWest p = true := by
  rfl
theorem dir218_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 218 245 .southEast || decide (bonus 218 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check999 p, rfl⟩
theorem dir218_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 218 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 218 243 .southWest || decide (bonus 218 p ≤ bonus 243 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1000 p, rfl⟩
theorem dir224_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 .north p = true := by
  change ((!walkGuard soko3_2.board support p 224 198 .north || decide (bonus 224 p ≤ bonus 198 p)) && ((PreciseRolling.stayTargets soko3_2.board 198 .north).all (fun landing => !pushGuard support p 224 198 172 landing || decide (bonus 224 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 198 + bonus 198 (change p 198 (some landing)))) && (pushTargets soko3_2.board 198 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 224 198 172 landing || decide (bonus 224 p ≤ 1 - Generated.soko3_2Potential.boulder 198 - Generated.soko3_2Potential.hole landing + bonus 198 (change p 198 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1001 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1002 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir224_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 .south p = true := by
  rfl
theorem dir224_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 .east p = true := by
  change ((!walkGuard soko3_2.board support p 224 225 .east || decide (bonus 224 p ≤ bonus 225 p)) && ((PreciseRolling.stayTargets soko3_2.board 225 .east).all (fun landing => !pushGuard support p 224 225 226 landing || decide (bonus 224 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 225 + bonus 225 (change p 225 (some landing)))) && (pushTargets soko3_2.board 225 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 224 225 226 landing || decide (bonus 224 p ≤ 1 - Generated.soko3_2Potential.boulder 225 - Generated.soko3_2Potential.hole landing + bonus 225 (change p 225 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1003 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1004 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir224_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 .west p = true := by
  rfl
theorem dir224_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 224 199 .northEast || decide (bonus 224 p ≤ bonus 199 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1005 p, rfl⟩
theorem dir224_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 .northWest p = true := by
  rfl
theorem dir224_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 .southEast p = true := by
  rfl
theorem dir224_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 224 .southWest p = true := by
  rfl
theorem dir225_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 .north p = true := by
  change ((!walkGuard soko3_2.board support p 225 199 .north || decide (bonus 225 p ≤ bonus 199 p)) && ((PreciseRolling.stayTargets soko3_2.board 199 .north).all (fun landing => !pushGuard support p 225 199 173 landing || decide (bonus 225 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some landing)))) && (pushTargets soko3_2.board 199 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 225 199 173 landing || decide (bonus 225 p ≤ 1 - Generated.soko3_2Potential.boulder 199 - Generated.soko3_2Potential.hole landing + bonus 199 (change p 199 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1006 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1007 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir225_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 .south p = true := by
  rfl
theorem dir225_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 .east p = true := by
  change ((!walkGuard soko3_2.board support p 225 226 .east || decide (bonus 225 p ≤ bonus 226 p)) && ((PreciseRolling.stayTargets soko3_2.board 226 .east).all (fun landing => !pushGuard support p 225 226 227 landing || decide (bonus 225 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 226 + bonus 226 (change p 226 (some landing)))) && (pushTargets soko3_2.board 226 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 225 226 227 landing || decide (bonus 225 p ≤ 1 - Generated.soko3_2Potential.boulder 226 - Generated.soko3_2Potential.hole landing + bonus 226 (change p 226 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1008 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1009 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir225_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 .west p = true := by
  change ((!walkGuard soko3_2.board support p 225 224 .west || decide (bonus 225 p ≤ bonus 224 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1010 p, rfl⟩
theorem dir225_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 225 200 .northEast || decide (bonus 225 p ≤ bonus 200 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1011 p, rfl⟩
theorem dir225_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 225 198 .northWest || decide (bonus 225 p ≤ bonus 198 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1012 p, rfl⟩
theorem dir225_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 .southEast p = true := by
  rfl
theorem dir225_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 225 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
