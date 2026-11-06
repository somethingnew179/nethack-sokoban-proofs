import NetHack.Sokoban32Refined.Directions03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir71_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 .north p = true := by
  change ((!walkGuard soko3_2.board support p 71 45 .north || decide (bonus 71 p ≤ bonus 45 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check155 p, rfl⟩
theorem dir71_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 .south p = true := by
  change ((!walkGuard soko3_2.board support p 71 97 .south || decide (bonus 71 p ≤ bonus 97 p)) && ((PreciseRolling.stayTargets soko3_2.board 97 .south).all (fun landing => !pushGuard support p 71 97 123 landing || decide (bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 97 + bonus 97 (change p 97 (some landing)))) && (pushTargets soko3_2.board 97 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 71 97 123 landing || decide (bonus 71 p ≤ 1 - Generated.soko3_2Potential.boulder 97 - Generated.soko3_2Potential.hole landing + bonus 97 (change p 97 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check156 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check157 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir71_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 .east p = true := by
  change ((!walkGuard soko3_2.board support p 71 72 .east || decide (bonus 71 p ≤ bonus 72 p)) && ((PreciseRolling.stayTargets soko3_2.board 72 .east).all (fun landing => !pushGuard support p 71 72 73 landing || decide (bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some landing)))) && (pushTargets soko3_2.board 72 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 71 72 73 landing || decide (bonus 71 p ≤ 1 - Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.hole landing + bonus 72 (change p 72 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check158 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check159 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir71_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 .west p = true := by
  change ((!walkGuard soko3_2.board support p 71 70 .west || decide (bonus 71 p ≤ bonus 70 p)) && ((PreciseRolling.stayTargets soko3_2.board 70 .west).all (fun landing => !pushGuard support p 71 70 69 landing || decide (bonus 71 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some landing)))) && (pushTargets soko3_2.board 70 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 71 70 69 landing || decide (bonus 71 p ≤ 1 - Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.hole landing + bonus 70 (change p 70 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check160 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check161 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir71_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 71 46 .northEast || decide (bonus 71 p ≤ bonus 46 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check162 p, rfl⟩
theorem dir71_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 71 44 .northWest || decide (bonus 71 p ≤ bonus 44 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check163 p, rfl⟩
theorem dir71_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 71 98 .southEast || decide (bonus 71 p ≤ bonus 98 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check164 p, rfl⟩
theorem dir71_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 71 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 71 96 .southWest || decide (bonus 71 p ≤ bonus 96 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check165 p, rfl⟩
theorem dir72_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 .north p = true := by
  change ((!walkGuard soko3_2.board support p 72 46 .north || decide (bonus 72 p ≤ bonus 46 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check166 p, rfl⟩
theorem dir72_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 .south p = true := by
  change ((!walkGuard soko3_2.board support p 72 98 .south || decide (bonus 72 p ≤ bonus 98 p)) && ((PreciseRolling.stayTargets soko3_2.board 98 .south).all (fun landing => !pushGuard support p 72 98 124 landing || decide (bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 98 + bonus 98 (change p 98 (some landing)))) && (pushTargets soko3_2.board 98 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 72 98 124 landing || decide (bonus 72 p ≤ 1 - Generated.soko3_2Potential.boulder 98 - Generated.soko3_2Potential.hole landing + bonus 98 (change p 98 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check167 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check168 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir72_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 .east p = true := by
  change ((!walkGuard soko3_2.board support p 72 73 .east || decide (bonus 72 p ≤ bonus 73 p)) && ((PreciseRolling.stayTargets soko3_2.board 73 .east).all (fun landing => !pushGuard support p 72 73 74 landing || decide (bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some landing)))) && (pushTargets soko3_2.board 73 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 72 73 74 landing || decide (bonus 72 p ≤ 1 - Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.hole landing + bonus 73 (change p 73 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check169 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check170 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir72_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 .west p = true := by
  change ((!walkGuard soko3_2.board support p 72 71 .west || decide (bonus 72 p ≤ bonus 71 p)) && ((PreciseRolling.stayTargets soko3_2.board 71 .west).all (fun landing => !pushGuard support p 72 71 70 landing || decide (bonus 72 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some landing)))) && (pushTargets soko3_2.board 71 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 72 71 70 landing || decide (bonus 72 p ≤ 1 - Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.hole landing + bonus 71 (change p 71 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check171 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check172 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir72_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 72 47 .northEast || decide (bonus 72 p ≤ bonus 47 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check173 p, rfl⟩
theorem dir72_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 72 45 .northWest || decide (bonus 72 p ≤ bonus 45 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check174 p, rfl⟩
theorem dir72_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 72 99 .southEast || decide (bonus 72 p ≤ bonus 99 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check175 p, rfl⟩
theorem dir72_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 72 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 72 97 .southWest || decide (bonus 72 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check176 p, rfl⟩
theorem dir73_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 .north p = true := by
  change ((!walkGuard soko3_2.board support p 73 47 .north || decide (bonus 73 p ≤ bonus 47 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check177 p, rfl⟩
theorem dir73_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 .south p = true := by
  change ((!walkGuard soko3_2.board support p 73 99 .south || decide (bonus 73 p ≤ bonus 99 p)) && ((PreciseRolling.stayTargets soko3_2.board 99 .south).all (fun landing => !pushGuard support p 73 99 125 landing || decide (bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 99 + bonus 99 (change p 99 (some landing)))) && (pushTargets soko3_2.board 99 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 73 99 125 landing || decide (bonus 73 p ≤ 1 - Generated.soko3_2Potential.boulder 99 - Generated.soko3_2Potential.hole landing + bonus 99 (change p 99 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check178 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check179 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir73_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 .east p = true := by
  change ((!walkGuard soko3_2.board support p 73 74 .east || decide (bonus 73 p ≤ bonus 74 p)) && ((PreciseRolling.stayTargets soko3_2.board 74 .east).all (fun landing => !pushGuard support p 73 74 75 landing || decide (bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some landing)))) && (pushTargets soko3_2.board 74 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 73 74 75 landing || decide (bonus 73 p ≤ 1 - Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.hole landing + bonus 74 (change p 74 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check180 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check181 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir73_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 .west p = true := by
  change ((!walkGuard soko3_2.board support p 73 72 .west || decide (bonus 73 p ≤ bonus 72 p)) && ((PreciseRolling.stayTargets soko3_2.board 72 .west).all (fun landing => !pushGuard support p 73 72 71 landing || decide (bonus 73 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 72 + bonus 72 (change p 72 (some landing)))) && (pushTargets soko3_2.board 72 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 73 72 71 landing || decide (bonus 73 p ≤ 1 - Generated.soko3_2Potential.boulder 72 - Generated.soko3_2Potential.hole landing + bonus 72 (change p 72 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check182 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check183 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir73_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 73 48 .northEast || decide (bonus 73 p ≤ bonus 48 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check184 p, rfl⟩
theorem dir73_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 73 46 .northWest || decide (bonus 73 p ≤ bonus 46 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check185 p, rfl⟩
theorem dir73_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 73 100 .southEast || decide (bonus 73 p ≤ bonus 100 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check186 p, rfl⟩
theorem dir73_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 73 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 73 98 .southWest || decide (bonus 73 p ≤ bonus 98 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check187 p, rfl⟩
theorem dir74_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 .north p = true := by
  change ((!walkGuard soko3_2.board support p 74 48 .north || decide (bonus 74 p ≤ bonus 48 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check188 p, rfl⟩
theorem dir74_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 .south p = true := by
  change ((!walkGuard soko3_2.board support p 74 100 .south || decide (bonus 74 p ≤ bonus 100 p)) && ((PreciseRolling.stayTargets soko3_2.board 100 .south).all (fun landing => !pushGuard support p 74 100 126 landing || decide (bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 100 + bonus 100 (change p 100 (some landing)))) && (pushTargets soko3_2.board 100 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 74 100 126 landing || decide (bonus 74 p ≤ 1 - Generated.soko3_2Potential.boulder 100 - Generated.soko3_2Potential.hole landing + bonus 100 (change p 100 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check189 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check190 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir74_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 .east p = true := by
  change ((!walkGuard soko3_2.board support p 74 75 .east || decide (bonus 74 p ≤ bonus 75 p)) && ((PreciseRolling.stayTargets soko3_2.board 75 .east).all (fun landing => !pushGuard support p 74 75 76 landing || decide (bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some landing)))) && (pushTargets soko3_2.board 75 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 74 75 76 landing || decide (bonus 74 p ≤ 1 - Generated.soko3_2Potential.boulder 75 - Generated.soko3_2Potential.hole landing + bonus 75 (change p 75 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check191 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check192 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir74_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 .west p = true := by
  change ((!walkGuard soko3_2.board support p 74 73 .west || decide (bonus 74 p ≤ bonus 73 p)) && ((PreciseRolling.stayTargets soko3_2.board 73 .west).all (fun landing => !pushGuard support p 74 73 72 landing || decide (bonus 74 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 73 + bonus 73 (change p 73 (some landing)))) && (pushTargets soko3_2.board 73 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 74 73 72 landing || decide (bonus 74 p ≤ 1 - Generated.soko3_2Potential.boulder 73 - Generated.soko3_2Potential.hole landing + bonus 73 (change p 73 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check193 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check194 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir74_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 74 49 .northEast || decide (bonus 74 p ≤ bonus 49 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check195 p, rfl⟩
theorem dir74_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 74 47 .northWest || decide (bonus 74 p ≤ bonus 47 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check196 p, rfl⟩
theorem dir74_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 74 101 .southEast || decide (bonus 74 p ≤ bonus 101 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check197 p, rfl⟩
theorem dir74_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 74 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 74 99 .southWest || decide (bonus 74 p ≤ bonus 99 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check198 p, rfl⟩
theorem dir75_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 .north p = true := by
  change ((!walkGuard soko3_2.board support p 75 49 .north || decide (bonus 75 p ≤ bonus 49 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check199 p, rfl⟩
theorem dir75_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 .south p = true := by
  change ((!walkGuard soko3_2.board support p 75 101 .south || decide (bonus 75 p ≤ bonus 101 p)) && ((PreciseRolling.stayTargets soko3_2.board 101 .south).all (fun landing => !pushGuard support p 75 101 127 landing || decide (bonus 75 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 101 + bonus 101 (change p 101 (some landing)))) && (pushTargets soko3_2.board 101 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 75 101 127 landing || decide (bonus 75 p ≤ 1 - Generated.soko3_2Potential.boulder 101 - Generated.soko3_2Potential.hole landing + bonus 101 (change p 101 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check200 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check201 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir75_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 .east p = true := by
  change ((!walkGuard soko3_2.board support p 75 76 .east || decide (bonus 75 p ≤ bonus 76 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check202 p, rfl⟩
theorem dir75_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 .west p = true := by
  change ((!walkGuard soko3_2.board support p 75 74 .west || decide (bonus 75 p ≤ bonus 74 p)) && ((PreciseRolling.stayTargets soko3_2.board 74 .west).all (fun landing => !pushGuard support p 75 74 73 landing || decide (bonus 75 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 74 + bonus 74 (change p 74 (some landing)))) && (pushTargets soko3_2.board 74 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 75 74 73 landing || decide (bonus 75 p ≤ 1 - Generated.soko3_2Potential.boulder 74 - Generated.soko3_2Potential.hole landing + bonus 74 (change p 74 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check203 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check204 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir75_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 75 50 .northEast || decide (bonus 75 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check205 p, rfl⟩
theorem dir75_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 75 48 .northWest || decide (bonus 75 p ≤ bonus 48 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check206 p, rfl⟩
theorem dir75_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 75 102 .southEast || decide (bonus 75 p ≤ bonus 102 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check207 p, rfl⟩
theorem dir75_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 75 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 75 100 .southWest || decide (bonus 75 p ≤ bonus 100 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check208 p, rfl⟩
theorem dir76_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 .north p = true := by
  change ((!walkGuard soko3_2.board support p 76 50 .north || decide (bonus 76 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check209 p, rfl⟩
theorem dir76_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 .south p = true := by
  change ((!walkGuard soko3_2.board support p 76 102 .south || decide (bonus 76 p ≤ bonus 102 p)) && ((PreciseRolling.stayTargets soko3_2.board 102 .south).all (fun landing => !pushGuard support p 76 102 128 landing || decide (bonus 76 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 102 + bonus 102 (change p 102 (some landing)))) && (pushTargets soko3_2.board 102 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 76 102 128 landing || decide (bonus 76 p ≤ 1 - Generated.soko3_2Potential.boulder 102 - Generated.soko3_2Potential.hole landing + bonus 102 (change p 102 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check210 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check211 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir76_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 .east p = true := by
  rfl
theorem dir76_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 .west p = true := by
  change ((!walkGuard soko3_2.board support p 76 75 .west || decide (bonus 76 p ≤ bonus 75 p)) && ((PreciseRolling.stayTargets soko3_2.board 75 .west).all (fun landing => !pushGuard support p 76 75 74 landing || decide (bonus 76 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 75 + bonus 75 (change p 75 (some landing)))) && (pushTargets soko3_2.board 75 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 76 75 74 landing || decide (bonus 76 p ≤ 1 - Generated.soko3_2Potential.boulder 75 - Generated.soko3_2Potential.hole landing + bonus 75 (change p 75 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check212 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check213 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir76_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 .northEast p = true := by
  rfl
theorem dir76_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 76 49 .northWest || decide (bonus 76 p ≤ bonus 49 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check214 p, rfl⟩
theorem dir76_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 .southEast p = true := by
  rfl
theorem dir76_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 76 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 76 101 .southWest || decide (bonus 76 p ≤ bonus 101 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check215 p, rfl⟩
end NetHack.Sokoban32Refined
