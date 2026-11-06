import NetHack.Sokoban12CostPartition.Directions06
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir143_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 .north p = true := by
  change ((!walkGuard soko1_2.board support p 143 117 .north || decide (bonus 143 p ≤ bonus 117 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check269 p, rfl⟩
theorem dir143_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 .south p = true := by
  change ((!walkGuard soko1_2.board support p 143 169 .south || decide (bonus 143 p ≤ bonus 169 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check270 p, rfl⟩
theorem dir143_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 .east p = true := by
  rfl
theorem dir143_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 .west p = true := by
  change ((!walkGuard soko1_2.board support p 143 142 .west || decide (bonus 143 p ≤ bonus 142 p)) && ((PreciseRolling.stayTargets soko1_2.board 142 .west).all (fun landing => !pushGuard support p 143 142 141 landing || decide (bonus 143 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some landing)))) && (pushTargets soko1_2.board 142 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 143 142 141 landing || decide (bonus 143 p ≤ 1 - Generated.soko1_2Potential.boulder 142 - Generated.soko1_2Potential.hole landing + bonus 142 (change p 142 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check271 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check272 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir143_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 .northEast p = true := by
  rfl
theorem dir143_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 143 116 .northWest || decide (bonus 143 p ≤ bonus 116 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check273 p, rfl⟩
theorem dir143_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 .southEast p = true := by
  rfl
theorem dir143_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 143 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 143 168 .southWest || decide (bonus 143 p ≤ bonus 168 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check274 p, rfl⟩
theorem dir154_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 .north p = true := by
  change ((!walkGuard soko1_2.board support p 154 128 .north || decide (bonus 154 p ≤ bonus 128 p)) && ((PreciseRolling.stayTargets soko1_2.board 128 .north).all (fun landing => !pushGuard support p 154 128 102 landing || decide (bonus 154 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 128 + bonus 128 (change p 128 (some landing)))) && (pushTargets soko1_2.board 128 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 154 128 102 landing || decide (bonus 154 p ≤ 1 - Generated.soko1_2Potential.boulder 128 - Generated.soko1_2Potential.hole landing + bonus 128 (change p 128 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check275 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check276 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir154_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 .south p = true := by
  change ((!walkGuard soko1_2.board support p 154 180 .south || decide (bonus 154 p ≤ bonus 180 p)) && ((PreciseRolling.stayTargets soko1_2.board 180 .south).all (fun landing => !pushGuard support p 154 180 206 landing || decide (bonus 154 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 180 + bonus 180 (change p 180 (some landing)))) && (pushTargets soko1_2.board 180 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 154 180 206 landing || decide (bonus 154 p ≤ 1 - Generated.soko1_2Potential.boulder 180 - Generated.soko1_2Potential.hole landing + bonus 180 (change p 180 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check277 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check278 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir154_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 .east p = true := by
  rfl
theorem dir154_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 .west p = true := by
  rfl
theorem dir154_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 .northEast p = true := by
  rfl
theorem dir154_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 .northWest p = true := by
  rfl
theorem dir154_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 .southEast p = true := by
  rfl
theorem dir154_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 154 .southWest p = true := by
  rfl
theorem dir157_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 .north p = true := by
  change ((!walkGuard soko1_2.board support p 157 131 .north || decide (bonus 157 p ≤ bonus 131 p)) && ((PreciseRolling.stayTargets soko1_2.board 131 .north).all (fun landing => !pushGuard support p 157 131 105 landing || decide (bonus 157 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 131 + bonus 131 (change p 131 (some landing)))) && (pushTargets soko1_2.board 131 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 157 131 105 landing || decide (bonus 157 p ≤ 1 - Generated.soko1_2Potential.boulder 131 - Generated.soko1_2Potential.hole landing + bonus 131 (change p 131 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check279 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check280 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir157_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 .south p = true := by
  rfl
theorem dir157_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 .east p = true := by
  change ((!walkGuard soko1_2.board support p 157 158 .east || decide (bonus 157 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko1_2.board 158 .east).all (fun landing => !pushGuard support p 157 158 159 landing || decide (bonus 157 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko1_2.board 158 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 157 158 159 landing || decide (bonus 157 p ≤ 1 - Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check281 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check282 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir157_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 .west p = true := by
  rfl
theorem dir157_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 157 132 .northEast || decide (bonus 157 p ≤ bonus 132 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check283 p, rfl⟩
theorem dir157_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 .northWest p = true := by
  rfl
theorem dir157_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 157 184 .southEast || decide (bonus 157 p ≤ bonus 184 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check284 p, rfl⟩
theorem dir157_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 157 .southWest p = true := by
  rfl
theorem dir158_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 .north p = true := by
  change ((!walkGuard soko1_2.board support p 158 132 .north || decide (bonus 158 p ≤ bonus 132 p)) && ((PreciseRolling.stayTargets soko1_2.board 132 .north).all (fun landing => !pushGuard support p 158 132 106 landing || decide (bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some landing)))) && (pushTargets soko1_2.board 132 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 158 132 106 landing || decide (bonus 158 p ≤ 1 - Generated.soko1_2Potential.boulder 132 - Generated.soko1_2Potential.hole landing + bonus 132 (change p 132 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check285 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check286 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 .south p = true := by
  change ((!walkGuard soko1_2.board support p 158 184 .south || decide (bonus 158 p ≤ bonus 184 p)) && ((PreciseRolling.stayTargets soko1_2.board 184 .south).all (fun landing => !pushGuard support p 158 184 210 landing || decide (bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 184 + bonus 184 (change p 184 (some landing)))) && (pushTargets soko1_2.board 184 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 158 184 210 landing || decide (bonus 158 p ≤ 1 - Generated.soko1_2Potential.boulder 184 - Generated.soko1_2Potential.hole landing + bonus 184 (change p 184 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check287 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check288 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 .east p = true := by
  change ((!walkGuard soko1_2.board support p 158 159 .east || decide (bonus 158 p ≤ bonus 159 p)) && ((PreciseRolling.stayTargets soko1_2.board 159 .east).all (fun landing => !pushGuard support p 158 159 160 landing || decide (bonus 158 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some landing)))) && (pushTargets soko1_2.board 159 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 158 159 160 landing || decide (bonus 158 p ≤ 1 - Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.hole landing + bonus 159 (change p 159 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check289 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check290 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir158_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 .west p = true := by
  change ((!walkGuard soko1_2.board support p 158 157 .west || decide (bonus 158 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check291 p, rfl⟩
theorem dir158_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 158 133 .northEast || decide (bonus 158 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check292 p, rfl⟩
theorem dir158_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 158 131 .northWest || decide (bonus 158 p ≤ bonus 131 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check293 p, rfl⟩
theorem dir158_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 158 185 .southEast || decide (bonus 158 p ≤ bonus 185 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check294 p, rfl⟩
theorem dir158_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 158 .southWest p = true := by
  rfl
theorem dir159_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 .north p = true := by
  change ((!walkGuard soko1_2.board support p 159 133 .north || decide (bonus 159 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check295 p, rfl⟩
theorem dir159_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 .south p = true := by
  change ((!walkGuard soko1_2.board support p 159 185 .south || decide (bonus 159 p ≤ bonus 185 p)) && ((PreciseRolling.stayTargets soko1_2.board 185 .south).all (fun landing => !pushGuard support p 159 185 211 landing || decide (bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 185 + bonus 185 (change p 185 (some landing)))) && (pushTargets soko1_2.board 185 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 159 185 211 landing || decide (bonus 159 p ≤ 1 - Generated.soko1_2Potential.boulder 185 - Generated.soko1_2Potential.hole landing + bonus 185 (change p 185 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check296 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check297 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir159_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 .east p = true := by
  change ((!walkGuard soko1_2.board support p 159 160 .east || decide (bonus 159 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko1_2.board 160 .east).all (fun landing => !pushGuard support p 159 160 161 landing || decide (bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko1_2.board 160 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 159 160 161 landing || decide (bonus 159 p ≤ 1 - Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check298 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check299 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir159_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 .west p = true := by
  change ((!walkGuard soko1_2.board support p 159 158 .west || decide (bonus 159 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko1_2.board 158 .west).all (fun landing => !pushGuard support p 159 158 157 landing || decide (bonus 159 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko1_2.board 158 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 159 158 157 landing || decide (bonus 159 p ≤ 1 - Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check300 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check301 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir159_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 159 134 .northEast || decide (bonus 159 p ≤ bonus 134 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check302 p, rfl⟩
theorem dir159_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 159 132 .northWest || decide (bonus 159 p ≤ bonus 132 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check303 p, rfl⟩
theorem dir159_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 159 186 .southEast || decide (bonus 159 p ≤ bonus 186 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check304 p, rfl⟩
theorem dir159_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 159 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 159 184 .southWest || decide (bonus 159 p ≤ bonus 184 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check305 p, rfl⟩
theorem dir160_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 .north p = true := by
  change ((!walkGuard soko1_2.board support p 160 134 .north || decide (bonus 160 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko1_2.board 134 .north).all (fun landing => !pushGuard support p 160 134 108 landing || decide (bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko1_2.board 134 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 160 134 108 landing || decide (bonus 160 p ≤ 1 - Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check306 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check307 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 .south p = true := by
  change ((!walkGuard soko1_2.board support p 160 186 .south || decide (bonus 160 p ≤ bonus 186 p)) && ((PreciseRolling.stayTargets soko1_2.board 186 .south).all (fun landing => !pushGuard support p 160 186 212 landing || decide (bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 186 + bonus 186 (change p 186 (some landing)))) && (pushTargets soko1_2.board 186 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 160 186 212 landing || decide (bonus 160 p ≤ 1 - Generated.soko1_2Potential.boulder 186 - Generated.soko1_2Potential.hole landing + bonus 186 (change p 186 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check308 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check309 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 .east p = true := by
  change ((!walkGuard soko1_2.board support p 160 161 .east || decide (bonus 160 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check310 p, rfl⟩
theorem dir160_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 .west p = true := by
  change ((!walkGuard soko1_2.board support p 160 159 .west || decide (bonus 160 p ≤ bonus 159 p)) && ((PreciseRolling.stayTargets soko1_2.board 159 .west).all (fun landing => !pushGuard support p 160 159 158 landing || decide (bonus 160 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some landing)))) && (pushTargets soko1_2.board 159 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 160 159 158 landing || decide (bonus 160 p ≤ 1 - Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.hole landing + bonus 159 (change p 159 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check311 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check312 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir160_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 160 135 .northEast || decide (bonus 160 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check313 p, rfl⟩
theorem dir160_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 160 133 .northWest || decide (bonus 160 p ≤ bonus 133 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check314 p, rfl⟩
theorem dir160_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 160 187 .southEast || decide (bonus 160 p ≤ bonus 187 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check315 p, rfl⟩
theorem dir160_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 160 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 160 185 .southWest || decide (bonus 160 p ≤ bonus 185 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check316 p, rfl⟩
end NetHack.Sokoban12CostPartition
