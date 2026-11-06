import NetHack.Sokoban32Refined.Directions21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir244_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 .north p = true := by
  change ((!walkGuard soko3_2.board support p 244 218 .north || decide (bonus 244 p ≤ bonus 218 p)) && ((PreciseRolling.stayTargets soko3_2.board 218 .north).all (fun landing => !pushGuard support p 244 218 192 landing || decide (bonus 244 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 218 + bonus 218 (change p 218 (some landing)))) && (pushTargets soko3_2.board 218 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 244 218 192 landing || decide (bonus 244 p ≤ 1 - Generated.soko3_2Potential.boulder 218 - Generated.soko3_2Potential.hole landing + bonus 218 (change p 218 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1102 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1103 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir244_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 .south p = true := by
  change ((!walkGuard soko3_2.board support p 244 270 .south || decide (bonus 244 p ≤ bonus 270 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1104 p, rfl⟩
theorem dir244_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 .east p = true := by
  change ((!walkGuard soko3_2.board support p 244 245 .east || decide (bonus 244 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1105 p, rfl⟩
theorem dir244_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 .west p = true := by
  change ((!walkGuard soko3_2.board support p 244 243 .west || decide (bonus 244 p ≤ bonus 243 p)) && ((PreciseRolling.stayTargets soko3_2.board 243 .west).all (fun landing => !pushGuard support p 244 243 242 landing || decide (bonus 244 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 243 + bonus 243 (change p 243 (some landing)))) && (pushTargets soko3_2.board 243 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 244 243 242 landing || decide (bonus 244 p ≤ 1 - Generated.soko3_2Potential.boulder 243 - Generated.soko3_2Potential.hole landing + bonus 243 (change p 243 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1106 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1107 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir244_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 .northEast p = true := by
  rfl
theorem dir244_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 .northWest p = true := by
  rfl
theorem dir244_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 244 271 .southEast || decide (bonus 244 p ≤ bonus 271 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1108 p, rfl⟩
theorem dir244_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 244 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 244 269 .southWest || decide (bonus 244 p ≤ bonus 269 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1109 p, rfl⟩
theorem dir245_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 .north p = true := by
  rfl
theorem dir245_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 .south p = true := by
  change ((!walkGuard soko3_2.board support p 245 271 .south || decide (bonus 245 p ≤ bonus 271 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1110 p, rfl⟩
theorem dir245_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 .east p = true := by
  rfl
theorem dir245_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 .west p = true := by
  change ((!walkGuard soko3_2.board support p 245 244 .west || decide (bonus 245 p ≤ bonus 244 p)) && ((PreciseRolling.stayTargets soko3_2.board 244 .west).all (fun landing => !pushGuard support p 245 244 243 landing || decide (bonus 245 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some landing)))) && (pushTargets soko3_2.board 244 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 245 244 243 landing || decide (bonus 245 p ≤ 1 - Generated.soko3_2Potential.boulder 244 - Generated.soko3_2Potential.hole landing + bonus 244 (change p 244 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1111 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1112 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir245_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 .northEast p = true := by
  rfl
theorem dir245_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 245 218 .northWest || decide (bonus 245 p ≤ bonus 218 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1113 p, rfl⟩
theorem dir245_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 245 272 .southEast || decide (bonus 245 p ≤ bonus 272 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1114 p, rfl⟩
theorem dir245_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 245 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 245 270 .southWest || decide (bonus 245 p ≤ bonus 270 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1115 p, rfl⟩
theorem dir261_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 .north p = true := by
  change ((!walkGuard soko3_2.board support p 261 235 .north || decide (bonus 261 p ≤ bonus 235 p)) && ((PreciseRolling.stayTargets soko3_2.board 235 .north).all (fun landing => !pushGuard support p 261 235 209 landing || decide (bonus 261 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 235 + bonus 235 (change p 235 (some landing)))) && (pushTargets soko3_2.board 235 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 261 235 209 landing || decide (bonus 261 p ≤ 1 - Generated.soko3_2Potential.boulder 235 - Generated.soko3_2Potential.hole landing + bonus 235 (change p 235 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1116 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1117 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir261_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 .south p = true := by
  change ((!walkGuard soko3_2.board support p 261 287 .south || decide (bonus 261 p ≤ bonus 287 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1118 p, rfl⟩
theorem dir261_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 .east p = true := by
  change ((!walkGuard soko3_2.board support p 261 262 .east || decide (bonus 261 p ≤ bonus 262 p)) && ((PreciseRolling.stayTargets soko3_2.board 262 .east).all (fun landing => !pushGuard support p 261 262 263 landing || decide (bonus 261 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 262 + bonus 262 (change p 262 (some landing)))) && (pushTargets soko3_2.board 262 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 261 262 263 landing || decide (bonus 261 p ≤ 1 - Generated.soko3_2Potential.boulder 262 - Generated.soko3_2Potential.hole landing + bonus 262 (change p 262 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1119 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1120 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir261_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 .west p = true := by
  rfl
theorem dir261_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 .northEast p = true := by
  rfl
theorem dir261_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 .northWest p = true := by
  rfl
theorem dir261_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 261 288 .southEast || decide (bonus 261 p ≤ bonus 288 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1121 p, rfl⟩
theorem dir261_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 261 .southWest p = true := by
  rfl
theorem dir262_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 .north p = true := by
  rfl
theorem dir262_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 .south p = true := by
  change ((!walkGuard soko3_2.board support p 262 288 .south || decide (bonus 262 p ≤ bonus 288 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1122 p, rfl⟩
theorem dir262_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 .east p = true := by
  change ((!walkGuard soko3_2.board support p 262 263 .east || decide (bonus 262 p ≤ bonus 263 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1123 p, rfl⟩
theorem dir262_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 .west p = true := by
  change ((!walkGuard soko3_2.board support p 262 261 .west || decide (bonus 262 p ≤ bonus 261 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1124 p, rfl⟩
theorem dir262_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 .northEast p = true := by
  rfl
theorem dir262_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 262 235 .northWest || decide (bonus 262 p ≤ bonus 235 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1125 p, rfl⟩
theorem dir262_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 262 289 .southEast || decide (bonus 262 p ≤ bonus 289 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1126 p, rfl⟩
theorem dir262_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 262 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 262 287 .southWest || decide (bonus 262 p ≤ bonus 287 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1127 p, rfl⟩
theorem dir263_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 .north p = true := by
  rfl
theorem dir263_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 .south p = true := by
  change ((!walkGuard soko3_2.board support p 263 289 .south || decide (bonus 263 p ≤ bonus 289 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1128 p, rfl⟩
theorem dir263_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 .east p = true := by
  rfl
theorem dir263_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 .west p = true := by
  change ((!walkGuard soko3_2.board support p 263 262 .west || decide (bonus 263 p ≤ bonus 262 p)) && ((PreciseRolling.stayTargets soko3_2.board 262 .west).all (fun landing => !pushGuard support p 263 262 261 landing || decide (bonus 263 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 262 + bonus 262 (change p 262 (some landing)))) && (pushTargets soko3_2.board 262 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 263 262 261 landing || decide (bonus 263 p ≤ 1 - Generated.soko3_2Potential.boulder 262 - Generated.soko3_2Potential.hole landing + bonus 262 (change p 262 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1129 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1130 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir263_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 .northEast p = true := by
  rfl
theorem dir263_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 .northWest p = true := by
  rfl
theorem dir263_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 263 290 .southEast || decide (bonus 263 p ≤ bonus 290 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1131 p, rfl⟩
theorem dir263_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 263 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 263 288 .southWest || decide (bonus 263 p ≤ bonus 288 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1132 p, rfl⟩
theorem dir265_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 .north p = true := by
  change ((!walkGuard soko3_2.board support p 265 239 .north || decide (bonus 265 p ≤ bonus 239 p)) && ((PreciseRolling.stayTargets soko3_2.board 239 .north).all (fun landing => !pushGuard support p 265 239 213 landing || decide (bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 239 + bonus 239 (change p 239 (some landing)))) && (pushTargets soko3_2.board 239 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 265 239 213 landing || decide (bonus 265 p ≤ 1 - Generated.soko3_2Potential.boulder 239 - Generated.soko3_2Potential.hole landing + bonus 239 (change p 239 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1133 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1134 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir265_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 .south p = true := by
  change ((!walkGuard soko3_2.board support p 265 291 .south || decide (bonus 265 p ≤ bonus 291 p)) && ((PreciseRolling.stayTargets soko3_2.board 291 .south).all (fun landing => !pushGuard support p 265 291 317 landing || decide (bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 291 + bonus 291 (change p 291 (some landing)))) && (pushTargets soko3_2.board 291 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 265 291 317 landing || decide (bonus 265 p ≤ 1 - Generated.soko3_2Potential.boulder 291 - Generated.soko3_2Potential.hole landing + bonus 291 (change p 291 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1135 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1136 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir265_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 .east p = true := by
  change ((!walkGuard soko3_2.board support p 265 266 .east || decide (bonus 265 p ≤ bonus 266 p)) && ((PreciseRolling.stayTargets soko3_2.board 266 .east).all (fun landing => !pushGuard support p 265 266 267 landing || decide (bonus 265 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 266 + bonus 266 (change p 266 (some landing)))) && (pushTargets soko3_2.board 266 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 265 266 267 landing || decide (bonus 265 p ≤ 1 - Generated.soko3_2Potential.boulder 266 - Generated.soko3_2Potential.hole landing + bonus 266 (change p 266 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1137 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1138 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir265_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 .west p = true := by
  rfl
theorem dir265_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 .northEast p = true := by
  rfl
theorem dir265_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 .northWest p = true := by
  rfl
theorem dir265_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 265 292 .southEast || decide (bonus 265 p ≤ bonus 292 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1139 p, rfl⟩
theorem dir265_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 265 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 265 290 .southWest || decide (bonus 265 p ≤ bonus 290 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1140 p, rfl⟩
end NetHack.Sokoban32Refined
