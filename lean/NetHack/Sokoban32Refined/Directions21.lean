import NetHack.Sokoban32Refined.Directions20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir232_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 .north p = true := by
  change ((!walkGuard soko3_2.board support p 232 206 .north || decide (bonus 232 p ≤ bonus 206 p)) && ((PreciseRolling.stayTargets soko3_2.board 206 .north).all (fun landing => !pushGuard support p 232 206 180 landing || decide (bonus 232 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 206 + bonus 206 (change p 206 (some landing)))) && (pushTargets soko3_2.board 206 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 232 206 180 landing || decide (bonus 232 p ≤ 1 - Generated.soko3_2Potential.boulder 206 - Generated.soko3_2Potential.hole landing + bonus 206 (change p 206 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1060 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1061 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir232_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 .south p = true := by
  rfl
theorem dir232_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 .east p = true := by
  rfl
theorem dir232_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 .west p = true := by
  change ((!walkGuard soko3_2.board support p 232 231 .west || decide (bonus 232 p ≤ bonus 231 p)) && ((PreciseRolling.stayTargets soko3_2.board 231 .west).all (fun landing => !pushGuard support p 232 231 230 landing || decide (bonus 232 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 231 + bonus 231 (change p 231 (some landing)))) && (pushTargets soko3_2.board 231 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 232 231 230 landing || decide (bonus 232 p ≤ 1 - Generated.soko3_2Potential.boulder 231 - Generated.soko3_2Potential.hole landing + bonus 231 (change p 231 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1062 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1063 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir232_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 .northEast p = true := by
  rfl
theorem dir232_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 232 205 .northWest || decide (bonus 232 p ≤ bonus 205 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1064 p, rfl⟩
theorem dir232_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 .southEast p = true := by
  rfl
theorem dir232_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 232 .southWest p = true := by
  rfl
theorem dir235_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 .north p = true := by
  change ((!walkGuard soko3_2.board support p 235 209 .north || decide (bonus 235 p ≤ bonus 209 p)) && ((PreciseRolling.stayTargets soko3_2.board 209 .north).all (fun landing => !pushGuard support p 235 209 183 landing || decide (bonus 235 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 209 + bonus 209 (change p 209 (some landing)))) && (pushTargets soko3_2.board 209 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 235 209 183 landing || decide (bonus 235 p ≤ 1 - Generated.soko3_2Potential.boulder 209 - Generated.soko3_2Potential.hole landing + bonus 209 (change p 209 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1065 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1066 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir235_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 .south p = true := by
  change ((!walkGuard soko3_2.board support p 235 261 .south || decide (bonus 235 p ≤ bonus 261 p)) && ((PreciseRolling.stayTargets soko3_2.board 261 .south).all (fun landing => !pushGuard support p 235 261 287 landing || decide (bonus 235 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 261 + bonus 261 (change p 261 (some landing)))) && (pushTargets soko3_2.board 261 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 235 261 287 landing || decide (bonus 235 p ≤ 1 - Generated.soko3_2Potential.boulder 261 - Generated.soko3_2Potential.hole landing + bonus 261 (change p 261 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1067 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1068 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir235_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 .east p = true := by
  rfl
theorem dir235_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 .west p = true := by
  rfl
theorem dir235_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 235 210 .northEast || decide (bonus 235 p ≤ bonus 210 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1069 p, rfl⟩
theorem dir235_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 .northWest p = true := by
  rfl
theorem dir235_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 235 262 .southEast || decide (bonus 235 p ≤ bonus 262 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1070 p, rfl⟩
theorem dir235_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 235 .southWest p = true := by
  rfl
theorem dir239_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 .north p = true := by
  change ((!walkGuard soko3_2.board support p 239 213 .north || decide (bonus 239 p ≤ bonus 213 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1071 p, rfl⟩
theorem dir239_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 .south p = true := by
  change ((!walkGuard soko3_2.board support p 239 265 .south || decide (bonus 239 p ≤ bonus 265 p)) && ((PreciseRolling.stayTargets soko3_2.board 265 .south).all (fun landing => !pushGuard support p 239 265 291 landing || decide (bonus 239 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 265 + bonus 265 (change p 265 (some landing)))) && (pushTargets soko3_2.board 265 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 239 265 291 landing || decide (bonus 239 p ≤ 1 - Generated.soko3_2Potential.boulder 265 - Generated.soko3_2Potential.hole landing + bonus 265 (change p 265 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1072 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1073 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir239_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 .east p = true := by
  rfl
theorem dir239_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 .west p = true := by
  rfl
theorem dir239_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 239 214 .northEast || decide (bonus 239 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1074 p, rfl⟩
theorem dir239_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 239 212 .northWest || decide (bonus 239 p ≤ bonus 212 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1075 p, rfl⟩
theorem dir239_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 239 266 .southEast || decide (bonus 239 p ≤ bonus 266 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1076 p, rfl⟩
theorem dir239_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 239 .southWest p = true := by
  rfl
theorem dir241_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 .north p = true := by
  change ((!walkGuard soko3_2.board support p 241 215 .north || decide (bonus 241 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko3_2.board 215 .north).all (fun landing => !pushGuard support p 241 215 189 landing || decide (bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko3_2.board 215 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 241 215 189 landing || decide (bonus 241 p ≤ 1 - Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1077 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1078 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir241_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 .south p = true := by
  change ((!walkGuard soko3_2.board support p 241 267 .south || decide (bonus 241 p ≤ bonus 267 p)) && ((PreciseRolling.stayTargets soko3_2.board 267 .south).all (fun landing => !pushGuard support p 241 267 293 landing || decide (bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 267 + bonus 267 (change p 267 (some landing)))) && (pushTargets soko3_2.board 267 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 241 267 293 landing || decide (bonus 241 p ≤ 1 - Generated.soko3_2Potential.boulder 267 - Generated.soko3_2Potential.hole landing + bonus 267 (change p 267 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1079 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1080 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir241_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 .east p = true := by
  change ((!walkGuard soko3_2.board support p 241 242 .east || decide (bonus 241 p ≤ bonus 242 p)) && ((PreciseRolling.stayTargets soko3_2.board 242 .east).all (fun landing => !pushGuard support p 241 242 243 landing || decide (bonus 241 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 242 + bonus 242 (change p 242 (some landing)))) && (pushTargets soko3_2.board 242 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 241 242 243 landing || decide (bonus 241 p ≤ 1 - Generated.soko3_2Potential.boulder 242 - Generated.soko3_2Potential.hole landing + bonus 242 (change p 242 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1081 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1082 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir241_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 .west p = true := by
  rfl
theorem dir241_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 241 216 .northEast || decide (bonus 241 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1083 p, rfl⟩
theorem dir241_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 241 214 .northWest || decide (bonus 241 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1084 p, rfl⟩
theorem dir241_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 .southEast p = true := by
  rfl
theorem dir241_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 241 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 241 266 .southWest || decide (bonus 241 p ≤ bonus 266 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1085 p, rfl⟩
theorem dir242_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 .north p = true := by
  change ((!walkGuard soko3_2.board support p 242 216 .north || decide (bonus 242 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1086 p, rfl⟩
theorem dir242_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 .south p = true := by
  rfl
theorem dir242_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 .east p = true := by
  change ((!walkGuard soko3_2.board support p 242 243 .east || decide (bonus 242 p ≤ bonus 243 p)) && ((PreciseRolling.stayTargets soko3_2.board 243 .east).all (fun landing => !pushGuard support p 242 243 244 landing || decide (bonus 242 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 243 + bonus 243 (change p 243 (some landing)))) && (pushTargets soko3_2.board 243 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 242 243 244 landing || decide (bonus 242 p ≤ 1 - Generated.soko3_2Potential.boulder 243 - Generated.soko3_2Potential.hole landing + bonus 243 (change p 243 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1087 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1088 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir242_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 .west p = true := by
  change ((!walkGuard soko3_2.board support p 242 241 .west || decide (bonus 242 p ≤ bonus 241 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1089 p, rfl⟩
theorem dir242_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 .northEast p = true := by
  rfl
theorem dir242_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 242 215 .northWest || decide (bonus 242 p ≤ bonus 215 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1090 p, rfl⟩
theorem dir242_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 242 269 .southEast || decide (bonus 242 p ≤ bonus 269 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1091 p, rfl⟩
theorem dir242_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 242 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 242 267 .southWest || decide (bonus 242 p ≤ bonus 267 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1092 p, rfl⟩
theorem dir243_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 .north p = true := by
  rfl
theorem dir243_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 .south p = true := by
  change ((!walkGuard soko3_2.board support p 243 269 .south || decide (bonus 243 p ≤ bonus 269 p)) && ((PreciseRolling.stayTargets soko3_2.board 269 .south).all (fun landing => !pushGuard support p 243 269 295 landing || decide (bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 269 + bonus 269 (change p 269 (some landing)))) && (pushTargets soko3_2.board 269 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 243 269 295 landing || decide (bonus 243 p ≤ 1 - Generated.soko3_2Potential.boulder 269 - Generated.soko3_2Potential.hole landing + bonus 269 (change p 269 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1093 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1094 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir243_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 .east p = true := by
  change ((!walkGuard soko3_2.board support p 243 244 .east || decide (bonus 243 p ≤ bonus 244 p)) && ((PreciseRolling.stayTargets soko3_2.board 244 .east).all (fun landing => !pushGuard support p 243 244 245 landing || decide (bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some landing)))) && (pushTargets soko3_2.board 244 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 243 244 245 landing || decide (bonus 243 p ≤ 1 - Generated.soko3_2Potential.boulder 244 - Generated.soko3_2Potential.hole landing + bonus 244 (change p 244 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1095 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1096 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir243_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 .west p = true := by
  change ((!walkGuard soko3_2.board support p 243 242 .west || decide (bonus 243 p ≤ bonus 242 p)) && ((PreciseRolling.stayTargets soko3_2.board 242 .west).all (fun landing => !pushGuard support p 243 242 241 landing || decide (bonus 243 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 242 + bonus 242 (change p 242 (some landing)))) && (pushTargets soko3_2.board 242 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 243 242 241 landing || decide (bonus 243 p ≤ 1 - Generated.soko3_2Potential.boulder 242 - Generated.soko3_2Potential.hole landing + bonus 242 (change p 242 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1097 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1098 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir243_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 243 218 .northEast || decide (bonus 243 p ≤ bonus 218 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1099 p, rfl⟩
theorem dir243_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 243 216 .northWest || decide (bonus 243 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1100 p, rfl⟩
theorem dir243_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 243 270 .southEast || decide (bonus 243 p ≤ bonus 270 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1101 p, rfl⟩
theorem dir243_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 243 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
