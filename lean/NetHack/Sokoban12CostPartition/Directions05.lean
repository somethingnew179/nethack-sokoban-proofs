import NetHack.Sokoban12CostPartition.Directions04
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir115_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 .north p = true := by
  rfl
theorem dir115_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 .south p = true := by
  change ((!walkGuard soko1_2.board support p 115 141 .south || decide (bonus 115 p ≤ bonus 141 p)) && ((PreciseRolling.stayTargets soko1_2.board 141 .south).all (fun landing => !pushGuard support p 115 141 167 landing || decide (bonus 115 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 141 + bonus 141 (change p 141 (some landing)))) && (pushTargets soko1_2.board 141 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 115 141 167 landing || decide (bonus 115 p ≤ 1 - Generated.soko1_2Potential.boulder 141 - Generated.soko1_2Potential.hole landing + bonus 141 (change p 141 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check183 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check184 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir115_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 .east p = true := by
  change ((!walkGuard soko1_2.board support p 115 116 .east || decide (bonus 115 p ≤ bonus 116 p)) && ((PreciseRolling.stayTargets soko1_2.board 116 .east).all (fun landing => !pushGuard support p 115 116 117 landing || decide (bonus 115 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 116 + bonus 116 (change p 116 (some landing)))) && (pushTargets soko1_2.board 116 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 115 116 117 landing || decide (bonus 115 p ≤ 1 - Generated.soko1_2Potential.boulder 116 - Generated.soko1_2Potential.hole landing + bonus 116 (change p 116 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check185 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check186 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir115_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 .west p = true := by
  rfl
theorem dir115_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 .northEast p = true := by
  rfl
theorem dir115_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 .northWest p = true := by
  rfl
theorem dir115_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 115 142 .southEast || decide (bonus 115 p ≤ bonus 142 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check187 p, rfl⟩
theorem dir115_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 115 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 115 140 .southWest || decide (bonus 115 p ≤ bonus 140 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check188 p, rfl⟩
theorem dir116_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 .north p = true := by
  rfl
theorem dir116_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 .south p = true := by
  change ((!walkGuard soko1_2.board support p 116 142 .south || decide (bonus 116 p ≤ bonus 142 p)) && ((PreciseRolling.stayTargets soko1_2.board 142 .south).all (fun landing => !pushGuard support p 116 142 168 landing || decide (bonus 116 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 142 + bonus 142 (change p 142 (some landing)))) && (pushTargets soko1_2.board 142 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 116 142 168 landing || decide (bonus 116 p ≤ 1 - Generated.soko1_2Potential.boulder 142 - Generated.soko1_2Potential.hole landing + bonus 142 (change p 142 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check189 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check190 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir116_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 .east p = true := by
  change ((!walkGuard soko1_2.board support p 116 117 .east || decide (bonus 116 p ≤ bonus 117 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check191 p, rfl⟩
theorem dir116_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 .west p = true := by
  change ((!walkGuard soko1_2.board support p 116 115 .west || decide (bonus 116 p ≤ bonus 115 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check192 p, rfl⟩
theorem dir116_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 .northEast p = true := by
  rfl
theorem dir116_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 .northWest p = true := by
  rfl
theorem dir116_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 116 143 .southEast || decide (bonus 116 p ≤ bonus 143 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check193 p, rfl⟩
theorem dir116_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 116 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 116 141 .southWest || decide (bonus 116 p ≤ bonus 141 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check194 p, rfl⟩
theorem dir117_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 .north p = true := by
  rfl
theorem dir117_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 .south p = true := by
  change ((!walkGuard soko1_2.board support p 117 143 .south || decide (bonus 117 p ≤ bonus 143 p)) && ((PreciseRolling.stayTargets soko1_2.board 143 .south).all (fun landing => !pushGuard support p 117 143 169 landing || decide (bonus 117 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 143 + bonus 143 (change p 143 (some landing)))) && (pushTargets soko1_2.board 143 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 117 143 169 landing || decide (bonus 117 p ≤ 1 - Generated.soko1_2Potential.boulder 143 - Generated.soko1_2Potential.hole landing + bonus 143 (change p 143 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check195 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check196 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir117_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 .east p = true := by
  rfl
theorem dir117_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 .west p = true := by
  change ((!walkGuard soko1_2.board support p 117 116 .west || decide (bonus 117 p ≤ bonus 116 p)) && ((PreciseRolling.stayTargets soko1_2.board 116 .west).all (fun landing => !pushGuard support p 117 116 115 landing || decide (bonus 117 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 116 + bonus 116 (change p 116 (some landing)))) && (pushTargets soko1_2.board 116 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 117 116 115 landing || decide (bonus 117 p ≤ 1 - Generated.soko1_2Potential.boulder 116 - Generated.soko1_2Potential.hole landing + bonus 116 (change p 116 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check197 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check198 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir117_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 .northEast p = true := by
  rfl
theorem dir117_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 .northWest p = true := by
  rfl
theorem dir117_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 .southEast p = true := by
  rfl
theorem dir117_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 117 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 117 142 .southWest || decide (bonus 117 p ≤ bonus 142 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check199 p, rfl⟩
theorem dir128_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 .north p = true := by
  change ((!walkGuard soko1_2.board support p 128 102 .north || decide (bonus 128 p ≤ bonus 102 p)) && ((PreciseRolling.stayTargets soko1_2.board 102 .north).all (fun landing => !pushGuard support p 128 102 76 landing || decide (bonus 128 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 102 + bonus 102 (change p 102 (some landing)))) && (pushTargets soko1_2.board 102 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 128 102 76 landing || decide (bonus 128 p ≤ 1 - Generated.soko1_2Potential.boulder 102 - Generated.soko1_2Potential.hole landing + bonus 102 (change p 102 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check200 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check201 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir128_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 .south p = true := by
  change ((!walkGuard soko1_2.board support p 128 154 .south || decide (bonus 128 p ≤ bonus 154 p)) && ((PreciseRolling.stayTargets soko1_2.board 154 .south).all (fun landing => !pushGuard support p 128 154 180 landing || decide (bonus 128 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 154 + bonus 154 (change p 154 (some landing)))) && (pushTargets soko1_2.board 154 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 128 154 180 landing || decide (bonus 128 p ≤ 1 - Generated.soko1_2Potential.boulder 154 - Generated.soko1_2Potential.hole landing + bonus 154 (change p 154 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check202 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check203 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir128_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 .east p = true := by
  rfl
theorem dir128_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 .west p = true := by
  rfl
theorem dir128_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 .northEast p = true := by
  rfl
theorem dir128_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 .northWest p = true := by
  rfl
theorem dir128_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 .southEast p = true := by
  rfl
theorem dir128_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 128 .southWest p = true := by
  rfl
theorem dir131_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 .north p = true := by
  change ((!walkGuard soko1_2.board support p 131 105 .north || decide (bonus 131 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check204 p, rfl⟩
theorem dir131_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 .south p = true := by
  change ((!walkGuard soko1_2.board support p 131 157 .south || decide (bonus 131 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check205 p, rfl⟩
theorem dir131_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 .east p = true := by
  change ((!walkGuard soko1_2.board support p 131 132 .east || decide (bonus 131 p ≤ bonus 132 p)) && ((PreciseRolling.stayTargets soko1_2.board 132 .east).all (fun landing => !pushGuard support p 131 132 133 landing || decide (bonus 131 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 132 + bonus 132 (change p 132 (some landing)))) && (pushTargets soko1_2.board 132 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 131 132 133 landing || decide (bonus 131 p ≤ 1 - Generated.soko1_2Potential.boulder 132 - Generated.soko1_2Potential.hole landing + bonus 132 (change p 132 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check206 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check207 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir131_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 .west p = true := by
  rfl
theorem dir131_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 131 106 .northEast || decide (bonus 131 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check208 p, rfl⟩
theorem dir131_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 .northWest p = true := by
  rfl
theorem dir131_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 131 158 .southEast || decide (bonus 131 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check209 p, rfl⟩
theorem dir131_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 131 .southWest p = true := by
  rfl
theorem dir132_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 .north p = true := by
  change ((!walkGuard soko1_2.board support p 132 106 .north || decide (bonus 132 p ≤ bonus 106 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check210 p, rfl⟩
theorem dir132_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 .south p = true := by
  change ((!walkGuard soko1_2.board support p 132 158 .south || decide (bonus 132 p ≤ bonus 158 p)) && ((PreciseRolling.stayTargets soko1_2.board 158 .south).all (fun landing => !pushGuard support p 132 158 184 landing || decide (bonus 132 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 158 + bonus 158 (change p 158 (some landing)))) && (pushTargets soko1_2.board 158 .south).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 132 158 184 landing || decide (bonus 132 p ≤ 1 - Generated.soko1_2Potential.boulder 158 - Generated.soko1_2Potential.hole landing + bonus 158 (change p 158 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check211 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check212 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir132_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 .east p = true := by
  change ((!walkGuard soko1_2.board support p 132 133 .east || decide (bonus 132 p ≤ bonus 133 p)) && ((PreciseRolling.stayTargets soko1_2.board 133 .east).all (fun landing => !pushGuard support p 132 133 134 landing || decide (bonus 132 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 133 + bonus 133 (change p 133 (some landing)))) && (pushTargets soko1_2.board 133 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 132 133 134 landing || decide (bonus 132 p ≤ 1 - Generated.soko1_2Potential.boulder 133 - Generated.soko1_2Potential.hole landing + bonus 133 (change p 133 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check213 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check214 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir132_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 .west p = true := by
  change ((!walkGuard soko1_2.board support p 132 131 .west || decide (bonus 132 p ≤ bonus 131 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check215 p, rfl⟩
theorem dir132_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 .northEast p = true := by
  rfl
theorem dir132_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 132 105 .northWest || decide (bonus 132 p ≤ bonus 105 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check216 p, rfl⟩
theorem dir132_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 .southEast p = true := by
  change ((!walkGuard soko1_2.board support p 132 159 .southEast || decide (bonus 132 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check217 p, rfl⟩
theorem dir132_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 132 .southWest p = true := by
  change ((!walkGuard soko1_2.board support p 132 157 .southWest || decide (bonus 132 p ≤ bonus 157 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check218 p, rfl⟩
end NetHack.Sokoban12CostPartition
