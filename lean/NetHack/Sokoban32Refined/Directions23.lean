import NetHack.Sokoban32Refined.Directions22
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir266_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 .north p = true := by
  rfl
theorem dir266_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 .south p = true := by
  change ((!walkGuard soko3_2.board support p 266 292 .south || decide (bonus 266 p ≤ bonus 292 p)) && ((PreciseRolling.stayTargets soko3_2.board 292 .south).all (fun landing => !pushGuard support p 266 292 318 landing || decide (bonus 266 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 292 + bonus 292 (change p 292 (some landing)))) && (pushTargets soko3_2.board 292 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 266 292 318 landing || decide (bonus 266 p ≤ 1 - Generated.soko3_2Potential.boulder 292 - Generated.soko3_2Potential.hole landing + bonus 292 (change p 292 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1141 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1142 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir266_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 .east p = true := by
  change ((!walkGuard soko3_2.board support p 266 267 .east || decide (bonus 266 p ≤ bonus 267 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1143 p, rfl⟩
theorem dir266_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 .west p = true := by
  change ((!walkGuard soko3_2.board support p 266 265 .west || decide (bonus 266 p ≤ bonus 265 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1144 p, rfl⟩
theorem dir266_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 266 241 .northEast || decide (bonus 266 p ≤ bonus 241 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1145 p, rfl⟩
theorem dir266_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 266 239 .northWest || decide (bonus 266 p ≤ bonus 239 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1146 p, rfl⟩
theorem dir266_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 266 293 .southEast || decide (bonus 266 p ≤ bonus 293 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1147 p, rfl⟩
theorem dir266_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 266 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 266 291 .southWest || decide (bonus 266 p ≤ bonus 291 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1148 p, rfl⟩
theorem dir267_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 .north p = true := by
  change ((!walkGuard soko3_2.board support p 267 241 .north || decide (bonus 267 p ≤ bonus 241 p)) && ((PreciseRolling.stayTargets soko3_2.board 241 .north).all (fun landing => !pushGuard support p 267 241 215 landing || decide (bonus 267 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 241 + bonus 241 (change p 241 (some landing)))) && (pushTargets soko3_2.board 241 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 267 241 215 landing || decide (bonus 267 p ≤ 1 - Generated.soko3_2Potential.boulder 241 - Generated.soko3_2Potential.hole landing + bonus 241 (change p 241 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1149 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1150 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir267_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 .south p = true := by
  change ((!walkGuard soko3_2.board support p 267 293 .south || decide (bonus 267 p ≤ bonus 293 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1151 p, rfl⟩
theorem dir267_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 .east p = true := by
  rfl
theorem dir267_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 .west p = true := by
  change ((!walkGuard soko3_2.board support p 267 266 .west || decide (bonus 267 p ≤ bonus 266 p)) && ((PreciseRolling.stayTargets soko3_2.board 266 .west).all (fun landing => !pushGuard support p 267 266 265 landing || decide (bonus 267 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 266 + bonus 266 (change p 266 (some landing)))) && (pushTargets soko3_2.board 266 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 267 266 265 landing || decide (bonus 267 p ≤ 1 - Generated.soko3_2Potential.boulder 266 - Generated.soko3_2Potential.hole landing + bonus 266 (change p 266 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1152 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1153 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir267_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 267 242 .northEast || decide (bonus 267 p ≤ bonus 242 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1154 p, rfl⟩
theorem dir267_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 .northWest p = true := by
  rfl
theorem dir267_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 267 294 .southEast || decide (bonus 267 p ≤ bonus 294 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1155 p, rfl⟩
theorem dir267_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 267 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 267 292 .southWest || decide (bonus 267 p ≤ bonus 292 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1156 p, rfl⟩
theorem dir269_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 .north p = true := by
  change ((!walkGuard soko3_2.board support p 269 243 .north || decide (bonus 269 p ≤ bonus 243 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1157 p, rfl⟩
theorem dir269_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 .south p = true := by
  change ((!walkGuard soko3_2.board support p 269 295 .south || decide (bonus 269 p ≤ bonus 295 p)) && ((PreciseRolling.stayTargets soko3_2.board 295 .south).all (fun landing => !pushGuard support p 269 295 321 landing || decide (bonus 269 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 295 + bonus 295 (change p 295 (some landing)))) && (pushTargets soko3_2.board 295 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 269 295 321 landing || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 295 - Generated.soko3_2Potential.hole landing + bonus 295 (change p 295 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1158 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1159 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir269_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 .east p = true := by
  change ((!walkGuard soko3_2.board support p 269 270 .east || decide (bonus 269 p ≤ bonus 270 p)) && ((PreciseRolling.stayTargets soko3_2.board 270 .east).all (fun landing => !pushGuard support p 269 270 271 landing || decide (bonus 269 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 270 + bonus 270 (change p 270 (some landing)))) && (pushTargets soko3_2.board 270 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 269 270 271 landing || decide (bonus 269 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole landing + bonus 270 (change p 270 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1160 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1161 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨(by rfl), (List.forall_mem_cons.mpr ⟨check1162 p, (List.forall_mem_cons.mpr ⟨check1163 p, (List.forall_mem_cons.mpr ⟨check1164 p, (List.forall_mem_cons.mpr ⟨check1165 p, (List.forall_mem_cons.mpr ⟨check1166 p, (List.forall_mem_cons.mpr ⟨check1167 p, (List.forall_mem_cons.mpr ⟨check1168 p, (List.forall_mem_cons.mpr ⟨check1169 p, (List.forall_mem_cons.mpr ⟨check1170 p, (List.forall_mem_cons.mpr ⟨check1171 p, (List.forall_mem_cons.mpr ⟨check1172 p, (List.forall_mem_cons.mpr ⟨check1173 p, (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
theorem dir269_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 .west p = true := by
  rfl
theorem dir269_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 269 244 .northEast || decide (bonus 269 p ≤ bonus 244 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1174 p, rfl⟩
theorem dir269_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 269 242 .northWest || decide (bonus 269 p ≤ bonus 242 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1175 p, rfl⟩
theorem dir269_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 .southEast p = true := by
  rfl
theorem dir269_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 269 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 269 294 .southWest || decide (bonus 269 p ≤ bonus 294 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1176 p, rfl⟩
theorem dir270_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 .north p = true := by
  change ((!walkGuard soko3_2.board support p 270 244 .north || decide (bonus 270 p ≤ bonus 244 p)) && ((PreciseRolling.stayTargets soko3_2.board 244 .north).all (fun landing => !pushGuard support p 270 244 218 landing || decide (bonus 270 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 244 + bonus 244 (change p 244 (some landing)))) && (pushTargets soko3_2.board 244 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 270 244 218 landing || decide (bonus 270 p ≤ 1 - Generated.soko3_2Potential.boulder 244 - Generated.soko3_2Potential.hole landing + bonus 244 (change p 244 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1177 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1178 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir270_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 .south p = true := by
  rfl
theorem dir270_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 .east p = true := by
  change ((!walkGuard soko3_2.board support p 270 271 .east || decide (bonus 270 p ≤ bonus 271 p)) && ((PreciseRolling.stayTargets soko3_2.board 271 .east).all (fun landing => !pushGuard support p 270 271 272 landing || decide (bonus 270 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 271 + bonus 271 (change p 271 (some landing)))) && (pushTargets soko3_2.board 271 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 270 271 272 landing || decide (bonus 270 p ≤ 1 - Generated.soko3_2Potential.boulder 271 - Generated.soko3_2Potential.hole landing + bonus 271 (change p 271 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1179 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1180 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1181 p, (by intro cell member; cases member)⟩)
theorem dir270_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 .west p = true := by
  change ((!walkGuard soko3_2.board support p 270 269 .west || decide (bonus 270 p ≤ bonus 269 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1182 p, rfl⟩
theorem dir270_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 270 245 .northEast || decide (bonus 270 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1183 p, rfl⟩
theorem dir270_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 270 243 .northWest || decide (bonus 270 p ≤ bonus 243 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1184 p, rfl⟩
theorem dir270_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 .southEast p = true := by
  rfl
theorem dir270_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 270 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 270 295 .southWest || decide (bonus 270 p ≤ bonus 295 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1185 p, rfl⟩
theorem dir271_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 .north p = true := by
  change ((!walkGuard soko3_2.board support p 271 245 .north || decide (bonus 271 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1186 p, rfl⟩
theorem dir271_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 .south p = true := by
  rfl
theorem dir271_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 .east p = true := by
  change ((!walkGuard soko3_2.board support p 271 272 .east || decide (bonus 271 p ≤ bonus 272 p)) && ((PreciseRolling.stayTargets soko3_2.board 272 .east).all (fun landing => !pushGuard support p 271 272 273 landing || decide (bonus 271 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 272 + bonus 272 (change p 272 (some landing)))) && (pushTargets soko3_2.board 272 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 271 272 273 landing || decide (bonus 271 p ≤ 1 - Generated.soko3_2Potential.boulder 272 - Generated.soko3_2Potential.hole landing + bonus 272 (change p 272 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1187 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1188 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1189 p, (by intro cell member; cases member)⟩)
theorem dir271_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 .west p = true := by
  change ((!walkGuard soko3_2.board support p 271 270 .west || decide (bonus 271 p ≤ bonus 270 p)) && ((PreciseRolling.stayTargets soko3_2.board 270 .west).all (fun landing => !pushGuard support p 271 270 269 landing || decide (bonus 271 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 270 + bonus 270 (change p 270 (some landing)))) && (pushTargets soko3_2.board 270 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 271 270 269 landing || decide (bonus 271 p ≤ 1 - Generated.soko3_2Potential.boulder 270 - Generated.soko3_2Potential.hole landing + bonus 270 (change p 270 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1190 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1191 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir271_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 .northEast p = true := by
  rfl
theorem dir271_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 271 244 .northWest || decide (bonus 271 p ≤ bonus 244 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1192 p, rfl⟩
theorem dir271_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 .southEast p = true := by
  rfl
theorem dir271_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 271 .southWest p = true := by
  rfl
theorem dir272_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 .north p = true := by
  rfl
theorem dir272_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 .south p = true := by
  rfl
theorem dir272_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 .east p = true := by
  change ((!walkGuard soko3_2.board support p 272 273 .east || decide (bonus 272 p ≤ bonus 273 p)) && ((PreciseRolling.stayTargets soko3_2.board 273 .east).all (fun landing => !pushGuard support p 272 273 274 landing || decide (bonus 272 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 273 + bonus 273 (change p 273 (some landing)))) && (pushTargets soko3_2.board 273 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 272 273 274 landing || decide (bonus 272 p ≤ 1 - Generated.soko3_2Potential.boulder 273 - Generated.soko3_2Potential.hole landing + bonus 273 (change p 273 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1193 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1194 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1195 p, (by intro cell member; cases member)⟩)
theorem dir272_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 .west p = true := by
  change ((!walkGuard soko3_2.board support p 272 271 .west || decide (bonus 272 p ≤ bonus 271 p)) && ((PreciseRolling.stayTargets soko3_2.board 271 .west).all (fun landing => !pushGuard support p 272 271 270 landing || decide (bonus 272 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 271 + bonus 271 (change p 271 (some landing)))) && (pushTargets soko3_2.board 271 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 272 271 270 landing || decide (bonus 272 p ≤ 1 - Generated.soko3_2Potential.boulder 271 - Generated.soko3_2Potential.hole landing + bonus 271 (change p 271 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1196 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1197 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir272_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 .northEast p = true := by
  rfl
theorem dir272_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 272 245 .northWest || decide (bonus 272 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1198 p, rfl⟩
theorem dir272_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 .southEast p = true := by
  rfl
theorem dir272_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 272 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
