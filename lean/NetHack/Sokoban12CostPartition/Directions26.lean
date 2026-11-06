import NetHack.Sokoban12CostPartition.Directions25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir408_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 .north p = true := by
  change ((!walkGuard soko1_2.board support p 408 382 .north || decide (bonus 408 p ≤ bonus 382 p)) && ((PreciseRolling.stayTargets soko1_2.board 382 .north).all (fun landing => !pushGuard support p 408 382 356 landing || decide (bonus 408 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 382 + bonus 382 (change p 382 (some landing)))) && (pushTargets soko1_2.board 382 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 408 382 356 landing || decide (bonus 408 p ≤ 1 - Generated.soko1_2Potential.boulder 382 - Generated.soko1_2Potential.hole landing + bonus 382 (change p 382 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1134 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1135 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir408_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 .south p = true := by
  rfl
theorem dir408_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 .east p = true := by
  change ((!walkGuard soko1_2.board support p 408 409 .east || decide (bonus 408 p ≤ bonus 409 p)) && ((PreciseRolling.stayTargets soko1_2.board 409 .east).all (fun landing => !pushGuard support p 408 409 410 landing || decide (bonus 408 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 409 + bonus 409 (change p 409 (some landing)))) && (pushTargets soko1_2.board 409 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 408 409 410 landing || decide (bonus 408 p ≤ 1 - Generated.soko1_2Potential.boulder 409 - Generated.soko1_2Potential.hole landing + bonus 409 (change p 409 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1136 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1137 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir408_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 .west p = true := by
  rfl
theorem dir408_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 408 383 .northEast || decide (bonus 408 p ≤ bonus 383 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1138 p, rfl⟩
theorem dir408_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 .northWest p = true := by
  rfl
theorem dir408_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 .southEast p = true := by
  rfl
theorem dir408_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 408 .southWest p = true := by
  rfl
theorem dir409_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 .north p = true := by
  change ((!walkGuard soko1_2.board support p 409 383 .north || decide (bonus 409 p ≤ bonus 383 p)) && ((PreciseRolling.stayTargets soko1_2.board 383 .north).all (fun landing => !pushGuard support p 409 383 357 landing || decide (bonus 409 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 383 + bonus 383 (change p 383 (some landing)))) && (pushTargets soko1_2.board 383 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 409 383 357 landing || decide (bonus 409 p ≤ 1 - Generated.soko1_2Potential.boulder 383 - Generated.soko1_2Potential.hole landing + bonus 383 (change p 383 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1139 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1140 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir409_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 .south p = true := by
  rfl
theorem dir409_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 .east p = true := by
  change ((!walkGuard soko1_2.board support p 409 410 .east || decide (bonus 409 p ≤ bonus 410 p)) && ((PreciseRolling.stayTargets soko1_2.board 410 .east).all (fun landing => !pushGuard support p 409 410 411 landing || decide (bonus 409 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 410 + bonus 410 (change p 410 (some landing)))) && (pushTargets soko1_2.board 410 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 409 410 411 landing || decide (bonus 409 p ≤ 1 - Generated.soko1_2Potential.boulder 410 - Generated.soko1_2Potential.hole landing + bonus 410 (change p 410 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1141 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1142 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir409_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 .west p = true := by
  change ((!walkGuard soko1_2.board support p 409 408 .west || decide (bonus 409 p ≤ bonus 408 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1143 p, rfl⟩
theorem dir409_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 409 384 .northEast || decide (bonus 409 p ≤ bonus 384 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1144 p, rfl⟩
theorem dir409_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 409 382 .northWest || decide (bonus 409 p ≤ bonus 382 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1145 p, rfl⟩
theorem dir409_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 .southEast p = true := by
  rfl
theorem dir409_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 409 .southWest p = true := by
  rfl
theorem dir410_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 .north p = true := by
  change ((!walkGuard soko1_2.board support p 410 384 .north || decide (bonus 410 p ≤ bonus 384 p)) && ((PreciseRolling.stayTargets soko1_2.board 384 .north).all (fun landing => !pushGuard support p 410 384 358 landing || decide (bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 384 + bonus 384 (change p 384 (some landing)))) && (pushTargets soko1_2.board 384 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 410 384 358 landing || decide (bonus 410 p ≤ 1 - Generated.soko1_2Potential.boulder 384 - Generated.soko1_2Potential.hole landing + bonus 384 (change p 384 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1146 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1147 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir410_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 .south p = true := by
  rfl
theorem dir410_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 .east p = true := by
  change ((!walkGuard soko1_2.board support p 410 411 .east || decide (bonus 410 p ≤ bonus 411 p)) && ((PreciseRolling.stayTargets soko1_2.board 411 .east).all (fun landing => !pushGuard support p 410 411 412 landing || decide (bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 411 + bonus 411 (change p 411 (some landing)))) && (pushTargets soko1_2.board 411 .east).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 410 411 412 landing || decide (bonus 410 p ≤ 1 - Generated.soko1_2Potential.boulder 411 - Generated.soko1_2Potential.hole landing + bonus 411 (change p 411 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1148 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1149 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir410_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 .west p = true := by
  change ((!walkGuard soko1_2.board support p 410 409 .west || decide (bonus 410 p ≤ bonus 409 p)) && ((PreciseRolling.stayTargets soko1_2.board 409 .west).all (fun landing => !pushGuard support p 410 409 408 landing || decide (bonus 410 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 409 + bonus 409 (change p 409 (some landing)))) && (pushTargets soko1_2.board 409 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 410 409 408 landing || decide (bonus 410 p ≤ 1 - Generated.soko1_2Potential.boulder 409 - Generated.soko1_2Potential.hole landing + bonus 409 (change p 409 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1150 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1151 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir410_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 410 385 .northEast || decide (bonus 410 p ≤ bonus 385 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1152 p, rfl⟩
theorem dir410_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 410 383 .northWest || decide (bonus 410 p ≤ bonus 383 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1153 p, rfl⟩
theorem dir410_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 .southEast p = true := by
  rfl
theorem dir410_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 410 .southWest p = true := by
  rfl
theorem dir411_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 .north p = true := by
  change ((!walkGuard soko1_2.board support p 411 385 .north || decide (bonus 411 p ≤ bonus 385 p)) && ((PreciseRolling.stayTargets soko1_2.board 385 .north).all (fun landing => !pushGuard support p 411 385 359 landing || decide (bonus 411 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 385 + bonus 385 (change p 385 (some landing)))) && (pushTargets soko1_2.board 385 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 411 385 359 landing || decide (bonus 411 p ≤ 1 - Generated.soko1_2Potential.boulder 385 - Generated.soko1_2Potential.hole landing + bonus 385 (change p 385 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1154 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1155 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir411_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 .south p = true := by
  rfl
theorem dir411_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 .east p = true := by
  change ((!walkGuard soko1_2.board support p 411 412 .east || decide (bonus 411 p ≤ bonus 412 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1156 p, rfl⟩
theorem dir411_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 .west p = true := by
  change ((!walkGuard soko1_2.board support p 411 410 .west || decide (bonus 411 p ≤ bonus 410 p)) && ((PreciseRolling.stayTargets soko1_2.board 410 .west).all (fun landing => !pushGuard support p 411 410 409 landing || decide (bonus 411 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 410 + bonus 410 (change p 410 (some landing)))) && (pushTargets soko1_2.board 410 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 411 410 409 landing || decide (bonus 411 p ≤ 1 - Generated.soko1_2Potential.boulder 410 - Generated.soko1_2Potential.hole landing + bonus 410 (change p 410 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1157 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1158 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir411_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 .northEast p = true := by
  change ((!walkGuard soko1_2.board support p 411 386 .northEast || decide (bonus 411 p ≤ bonus 386 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1159 p, rfl⟩
theorem dir411_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 411 384 .northWest || decide (bonus 411 p ≤ bonus 384 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1160 p, rfl⟩
theorem dir411_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 .southEast p = true := by
  rfl
theorem dir411_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 411 .southWest p = true := by
  rfl
theorem dir412_north (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 .north p = true := by
  change ((!walkGuard soko1_2.board support p 412 386 .north || decide (bonus 412 p ≤ bonus 386 p)) && ((PreciseRolling.stayTargets soko1_2.board 386 .north).all (fun landing => !pushGuard support p 412 386 360 landing || decide (bonus 412 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 386 + bonus 386 (change p 386 (some landing)))) && (pushTargets soko1_2.board 386 .north).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 412 386 360 landing || decide (bonus 412 p ≤ 1 - Generated.soko1_2Potential.boulder 386 - Generated.soko1_2Potential.hole landing + bonus 386 (change p 386 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1161 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1162 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir412_south (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 .south p = true := by
  rfl
theorem dir412_east (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 .east p = true := by
  rfl
theorem dir412_west (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 .west p = true := by
  change ((!walkGuard soko1_2.board support p 412 411 .west || decide (bonus 412 p ≤ bonus 411 p)) && ((PreciseRolling.stayTargets soko1_2.board 411 .west).all (fun landing => !pushGuard support p 412 411 410 landing || decide (bonus 412 p ≤ 1 + Generated.soko1_2Potential.boulder landing - Generated.soko1_2Potential.boulder 411 + bonus 411 (change p 411 (some landing)))) && (pushTargets soko1_2.board 411 .west).all (fun landing => !soko1_2.initial.holes.contains landing || !pushGuard support p 412 411 410 landing || decide (bonus 412 p ≤ 1 - Generated.soko1_2Potential.boulder 411 - Generated.soko1_2Potential.hole landing + bonus 411 (change p 411 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check1163 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check1164 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir412_northEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 .northEast p = true := by
  rfl
theorem dir412_northWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 .northWest p = true := by
  change ((!walkGuard soko1_2.board support p 412 385 .northWest || decide (bonus 412 p ≤ bonus 385 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check1165 p, rfl⟩
theorem dir412_southEast (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 .southEast p = true := by
  rfl
theorem dir412_southWest (p : Pattern) : directionCheck soko1_2.board soko1_2.initial.holes Generated.soko1_2Potential support bonus 412 .southWest p = true := by
  rfl
end NetHack.Sokoban12CostPartition
