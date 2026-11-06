import NetHack.Sokoban12CostPartition.Directions05
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir133_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 .north p = true := by
  rfl
theorem dir133_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 .south p = true := by
  change ((!walkGuard soko1_2.board support p 133 159 .south || decide (bonus 133 p ≤ bonus 159 p)) && ((PreciseRolling.stayTargets soko1_2.board 159 .south).all (fun landing => !pushGuard support p 133 159 185 landing || decide (bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 159 + bonus 159 (change p 159 (some landing)))) && (pushTargets soko1_2.board 159 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 133 159 185 landing || decide (bonus 133 p ≤ 1 - Generated.soko1_2Potential.boulder 159 - Generated.soko1_2Potential.hole landing + bonus 159 (change p 159 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check219 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check220 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir133_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 .east p = true := by
  change ((!walkGuard soko1_2.board support p 133 134 .east || decide (bonus 133 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko1_2.board 134 .east).all (fun landing => !pushGuard support p 133 134 135 landing || decide (bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko1_2.board 134 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 133 134 135 landing || decide (bonus 133 p ≤ 1 - Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check221 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check222 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir133_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 .west p = true := by
  change ((!walkGuard soko1_2.board support p 133 132 .west || decide (bonus 133 p ≤ bonus 132 p)) && ((PreciseRolling.stayTargets soko1_2.board 132 .west).all (fun landing => !pushGuard support p 133 132 131 landing || decide (bonus 133 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some landing)))) && (pushTargets soko1_2.board 132 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 133 132 131 landing || decide (bonus 133 p ≤ 1 - Generated.soko1_2Potential.boulder 132 - Generated.soko1_2Potential.hole landing + bonus 132 (change p 132 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check223 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check224 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir133_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 133 108 .northEast || decide (bonus 133 p ≤ bonus 108 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check225 p, rfl⟩
theorem dir133_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 133 106 .northWest || decide (bonus 133 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check226 p, rfl⟩
theorem dir133_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 133 160 .southEast || decide (bonus 133 p ≤ bonus 160 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check227 p, rfl⟩
theorem dir133_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 133 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 133 158 .southWest || decide (bonus 133 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check228 p, rfl⟩
theorem dir134_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 .north p = true := by
  change ((!walkGuard soko1_2.board support p 134 108 .north || decide (bonus 134 p ≤ bonus 108 p)) && ((PreciseRolling.stayTargets soko1_2.board 108 .north).all (fun landing => !pushGuard support p 134 108 82 landing || decide (bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 108 + bonus 108 (change p 108 (some landing)))) && (pushTargets soko1_2.board 108 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 134 108 82 landing || decide (bonus 134 p ≤ 1 - Generated.soko1_2Potential.boulder 108 - Generated.soko1_2Potential.hole landing + bonus 108 (change p 108 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check229 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check230 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir134_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 .south p = true := by
  change ((!walkGuard soko1_2.board support p 134 160 .south || decide (bonus 134 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko1_2.board 160 .south).all (fun landing => !pushGuard support p 134 160 186 landing || decide (bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko1_2.board 160 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 134 160 186 landing || decide (bonus 134 p ≤ 1 - Generated.soko1_2Potential.boulder 160 - Generated.soko1_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check231 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check232 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir134_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 .east p = true := by
  change ((!walkGuard soko1_2.board support p 134 135 .east || decide (bonus 134 p ≤ bonus 135 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check233 p, rfl⟩
theorem dir134_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 .west p = true := by
  change ((!walkGuard soko1_2.board support p 134 133 .west || decide (bonus 134 p ≤ bonus 133 p)) && ((PreciseRolling.stayTargets soko1_2.board 133 .west).all (fun landing => !pushGuard support p 134 133 132 landing || decide (bonus 134 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 133 + bonus 133 (change p 133 (some landing)))) && (pushTargets soko1_2.board 133 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 134 133 132 landing || decide (bonus 134 p ≤ 1 - Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.hole landing + bonus 133 (change p 133 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check234 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check235 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir134_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 .northEast p = true := by
  rfl
theorem dir134_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 .northWest p = true := by
  rfl
theorem dir134_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 134 161 .southEast || decide (bonus 134 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check236 p, rfl⟩
theorem dir134_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 134 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 134 159 .southWest || decide (bonus 134 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check237 p, rfl⟩
theorem dir135_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 .north p = true := by
  rfl
theorem dir135_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 .south p = true := by
  change ((!walkGuard soko1_2.board support p 135 161 .south || decide (bonus 135 p ≤ bonus 161 p)) && ((PreciseRolling.stayTargets soko1_2.board 161 .south).all (fun landing => !pushGuard support p 135 161 187 landing || decide (bonus 135 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 161 + bonus 161 (change p 161 (some landing)))) && (pushTargets soko1_2.board 161 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 135 161 187 landing || decide (bonus 135 p ≤ 1 - Generated.soko1_2Potential.boulder 161 - Generated.soko1_2Potential.hole landing + bonus 161 (change p 161 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check238 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check239 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir135_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 .east p = true := by
  rfl
theorem dir135_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 .west p = true := by
  change ((!walkGuard soko1_2.board support p 135 134 .west || decide (bonus 135 p ≤ bonus 134 p)) && ((PreciseRolling.stayTargets soko1_2.board 134 .west).all (fun landing => !pushGuard support p 135 134 133 landing || decide (bonus 135 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 134 + bonus 134 (change p 134 (some landing)))) && (pushTargets soko1_2.board 134 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 135 134 133 landing || decide (bonus 135 p ≤ 1 - Generated.soko1_2Potential.boulder 134 - Generated.soko1_2Potential.hole landing + bonus 134 (change p 134 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check240 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check241 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir135_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 .northEast p = true := by
  rfl
theorem dir135_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 135 108 .northWest || decide (bonus 135 p ≤ bonus 108 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check242 p, rfl⟩
theorem dir135_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 .southEast p = true := by
  rfl
theorem dir135_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 135 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 135 160 .southWest || decide (bonus 135 p ≤ bonus 160 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check243 p, rfl⟩
theorem dir140_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 .north p = true := by
  rfl
theorem dir140_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 .south p = true := by
  change ((!walkGuard soko1_2.board support p 140 166 .south || decide (bonus 140 p ≤ bonus 166 p)) && ((PreciseRolling.stayTargets soko1_2.board 166 .south).all (fun landing => !pushGuard support p 140 166 192 landing || decide (bonus 140 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 166 + bonus 166 (change p 166 (some landing)))) && (pushTargets soko1_2.board 166 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 140 166 192 landing || decide (bonus 140 p ≤ 1 - Generated.soko1_2Potential.boulder 166 - Generated.soko1_2Potential.hole landing + bonus 166 (change p 166 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check244 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check245 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir140_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 .east p = true := by
  change ((!walkGuard soko1_2.board support p 140 141 .east || decide (bonus 140 p ≤ bonus 141 p)) && ((PreciseRolling.stayTargets soko1_2.board 141 .east).all (fun landing => !pushGuard support p 140 141 142 landing || decide (bonus 140 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some landing)))) && (pushTargets soko1_2.board 141 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 140 141 142 landing || decide (bonus 140 p ≤ 1 - Generated.soko1_2Potential.boulder 141 - Generated.soko1_2Potential.hole landing + bonus 141 (change p 141 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check246 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check247 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir140_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 .west p = true := by
  rfl
theorem dir140_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 140 115 .northEast || decide (bonus 140 p ≤ bonus 115 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check248 p, rfl⟩
theorem dir140_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 .northWest p = true := by
  rfl
theorem dir140_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 140 167 .southEast || decide (bonus 140 p ≤ bonus 167 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check249 p, rfl⟩
theorem dir140_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 140 .southWest p = true := by
  rfl
theorem dir141_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 .north p = true := by
  change ((!walkGuard soko1_2.board support p 141 115 .north || decide (bonus 141 p ≤ bonus 115 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check250 p, rfl⟩
theorem dir141_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 .south p = true := by
  change ((!walkGuard soko1_2.board support p 141 167 .south || decide (bonus 141 p ≤ bonus 167 p)) && ((PreciseRolling.stayTargets soko1_2.board 167 .south).all (fun landing => !pushGuard support p 141 167 193 landing || decide (bonus 141 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 167 + bonus 167 (change p 167 (some landing)))) && (pushTargets soko1_2.board 167 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 141 167 193 landing || decide (bonus 141 p ≤ 1 - Generated.soko1_2Potential.boulder 167 - Generated.soko1_2Potential.hole landing + bonus 167 (change p 167 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check251 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check252 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir141_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 .east p = true := by
  change ((!walkGuard soko1_2.board support p 141 142 .east || decide (bonus 141 p ≤ bonus 142 p)) && ((PreciseRolling.stayTargets soko1_2.board 142 .east).all (fun landing => !pushGuard support p 141 142 143 landing || decide (bonus 141 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some landing)))) && (pushTargets soko1_2.board 142 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 141 142 143 landing || decide (bonus 141 p ≤ 1 - Generated.soko1_2Potential.boulder 142 - Generated.soko1_2Potential.hole landing + bonus 142 (change p 142 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check253 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check254 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir141_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 .west p = true := by
  change ((!walkGuard soko1_2.board support p 141 140 .west || decide (bonus 141 p ≤ bonus 140 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check255 p, rfl⟩
theorem dir141_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 141 116 .northEast || decide (bonus 141 p ≤ bonus 116 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check256 p, rfl⟩
theorem dir141_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 .northWest p = true := by
  rfl
theorem dir141_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 141 168 .southEast || decide (bonus 141 p ≤ bonus 168 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check257 p, rfl⟩
theorem dir141_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 141 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 141 166 .southWest || decide (bonus 141 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check258 p, rfl⟩
theorem dir142_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 .north p = true := by
  change ((!walkGuard soko1_2.board support p 142 116 .north || decide (bonus 142 p ≤ bonus 116 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check259 p, rfl⟩
theorem dir142_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 .south p = true := by
  change ((!walkGuard soko1_2.board support p 142 168 .south || decide (bonus 142 p ≤ bonus 168 p)) && ((PreciseRolling.stayTargets soko1_2.board 168 .south).all (fun landing => !pushGuard support p 142 168 194 landing || decide (bonus 142 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 168 + bonus 168 (change p 168 (some landing)))) && (pushTargets soko1_2.board 168 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 142 168 194 landing || decide (bonus 142 p ≤ 1 - Generated.soko1_2Potential.boulder 168 - Generated.soko1_2Potential.hole landing + bonus 168 (change p 168 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check260 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check261 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir142_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 .east p = true := by
  change ((!walkGuard soko1_2.board support p 142 143 .east || decide (bonus 142 p ≤ bonus 143 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check262 p, rfl⟩
theorem dir142_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 .west p = true := by
  change ((!walkGuard soko1_2.board support p 142 141 .west || decide (bonus 142 p ≤ bonus 141 p)) && ((PreciseRolling.stayTargets soko1_2.board 141 .west).all (fun landing => !pushGuard support p 142 141 140 landing || decide (bonus 142 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some landing)))) && (pushTargets soko1_2.board 141 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 142 141 140 landing || decide (bonus 142 p ≤ 1 - Generated.soko1_2Potential.boulder 141 - Generated.soko1_2Potential.hole landing + bonus 141 (change p 141 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check263 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check264 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir142_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 142 117 .northEast || decide (bonus 142 p ≤ bonus 117 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check265 p, rfl⟩
theorem dir142_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 142 115 .northWest || decide (bonus 142 p ≤ bonus 115 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check266 p, rfl⟩
theorem dir142_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 142 169 .southEast || decide (bonus 142 p ≤ bonus 169 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check267 p, rfl⟩
theorem dir142_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 142 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 142 167 .southWest || decide (bonus 142 p ≤ bonus 167 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check268 p, rfl⟩
end NetHack.Sokoban12CostPartition
