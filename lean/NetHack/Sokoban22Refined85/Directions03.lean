import NetHack.Sokoban22Refined85.Directions02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir74_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 .north p = true := by
  change ((!walkGuard soko2_2.board support p 74 52 .north || decide (bonus 74 p ≤ bonus 52 p)) && ((PreciseRolling.stayTargets soko2_2.board 52 .north).all (fun landing => !pushGuard support p 74 52 30 landing || decide (bonus 74 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 52 + bonus 52 (change p 52 (some landing)))) && (pushTargets soko2_2.board 52 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 74 52 30 landing || decide (bonus 74 p ≤ 1 - Generated.soko2_2Potential.boulder 52 - Generated.soko2_2Potential.hole landing + bonus 52 (change p 52 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check127 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check128 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir74_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 .south p = true := by
  change ((!walkGuard soko2_2.board support p 74 96 .south || decide (bonus 74 p ≤ bonus 96 p)) && ((PreciseRolling.stayTargets soko2_2.board 96 .south).all (fun landing => !pushGuard support p 74 96 118 landing || decide (bonus 74 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 96 + bonus 96 (change p 96 (some landing)))) && (pushTargets soko2_2.board 96 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 74 96 118 landing || decide (bonus 74 p ≤ 1 - Generated.soko2_2Potential.boulder 96 - Generated.soko2_2Potential.hole landing + bonus 96 (change p 96 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check129 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check130 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir74_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 .east p = true := by
  rfl
theorem dir74_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 .west p = true := by
  change ((!walkGuard soko2_2.board support p 74 73 .west || decide (bonus 74 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check131 p, rfl⟩
theorem dir74_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 .northEast p = true := by
  rfl
theorem dir74_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 74 51 .northWest || decide (bonus 74 p ≤ bonus 51 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check132 p, rfl⟩
theorem dir74_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 74 97 .southEast || decide (bonus 74 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check133 p, rfl⟩
theorem dir74_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 74 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 74 95 .southWest || decide (bonus 74 p ≤ bonus 95 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check134 p, rfl⟩
theorem dir76_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 .north p = true := by
  rfl
theorem dir76_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 .south p = true := by
  change ((!walkGuard soko2_2.board support p 76 98 .south || decide (bonus 76 p ≤ bonus 98 p)) && ((PreciseRolling.stayTargets soko2_2.board 98 .south).all (fun landing => !pushGuard support p 76 98 120 landing || decide (bonus 76 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 98 + bonus 98 (change p 98 (some landing)))) && (pushTargets soko2_2.board 98 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 76 98 120 landing || decide (bonus 76 p ≤ 1 - Generated.soko2_2Potential.boulder 98 - Generated.soko2_2Potential.hole landing + bonus 98 (change p 98 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check135 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check136 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir76_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 .east p = true := by
  rfl
theorem dir76_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 .west p = true := by
  rfl
theorem dir76_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 .northEast p = true := by
  rfl
theorem dir76_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 .northWest p = true := by
  rfl
theorem dir76_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 .southEast p = true := by
  rfl
theorem dir76_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 76 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 76 97 .southWest || decide (bonus 76 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check137 p, rfl⟩
theorem dir78_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 .north p = true := by
  rfl
theorem dir78_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 .south p = true := by
  change ((!walkGuard soko2_2.board support p 78 100 .south || decide (bonus 78 p ≤ bonus 100 p)) && ((PreciseRolling.stayTargets soko2_2.board 100 .south).all (fun landing => !pushGuard support p 78 100 122 landing || decide (bonus 78 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 100 + bonus 100 (change p 100 (some landing)))) && (pushTargets soko2_2.board 100 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 78 100 122 landing || decide (bonus 78 p ≤ 1 - Generated.soko2_2Potential.boulder 100 - Generated.soko2_2Potential.hole landing + bonus 100 (change p 100 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check138 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check139 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir78_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 .east p = true := by
  change ((!walkGuard soko2_2.board support p 78 79 .east || decide (bonus 78 p ≤ bonus 79 p)) && ((PreciseRolling.stayTargets soko2_2.board 79 .east).all (fun landing => !pushGuard support p 78 79 80 landing || decide (bonus 78 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 79 + bonus 79 (change p 79 (some landing)))) && (pushTargets soko2_2.board 79 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 78 79 80 landing || decide (bonus 78 p ≤ 1 - Generated.soko2_2Potential.boulder 79 - Generated.soko2_2Potential.hole landing + bonus 79 (change p 79 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check140 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check141 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir78_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 .west p = true := by
  rfl
theorem dir78_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 .northEast p = true := by
  rfl
theorem dir78_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 .northWest p = true := by
  rfl
theorem dir78_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 78 101 .southEast || decide (bonus 78 p ≤ bonus 101 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check142 p, rfl⟩
theorem dir78_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 78 .southWest p = true := by
  rfl
theorem dir79_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 .north p = true := by
  rfl
theorem dir79_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 .south p = true := by
  change ((!walkGuard soko2_2.board support p 79 101 .south || decide (bonus 79 p ≤ bonus 101 p)) && ((PreciseRolling.stayTargets soko2_2.board 101 .south).all (fun landing => !pushGuard support p 79 101 123 landing || decide (bonus 79 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 101 + bonus 101 (change p 101 (some landing)))) && (pushTargets soko2_2.board 101 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 79 101 123 landing || decide (bonus 79 p ≤ 1 - Generated.soko2_2Potential.boulder 101 - Generated.soko2_2Potential.hole landing + bonus 101 (change p 101 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check143 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check144 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir79_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 .east p = true := by
  change ((!walkGuard soko2_2.board support p 79 80 .east || decide (bonus 79 p ≤ bonus 80 p)) && ((PreciseRolling.stayTargets soko2_2.board 80 .east).all (fun landing => !pushGuard support p 79 80 81 landing || decide (bonus 79 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 80 + bonus 80 (change p 80 (some landing)))) && (pushTargets soko2_2.board 80 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 79 80 81 landing || decide (bonus 79 p ≤ 1 - Generated.soko2_2Potential.boulder 80 - Generated.soko2_2Potential.hole landing + bonus 80 (change p 80 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check145 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check146 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir79_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 .west p = true := by
  change ((!walkGuard soko2_2.board support p 79 78 .west || decide (bonus 79 p ≤ bonus 78 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check147 p, rfl⟩
theorem dir79_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 .northEast p = true := by
  rfl
theorem dir79_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 .northWest p = true := by
  rfl
theorem dir79_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 79 102 .southEast || decide (bonus 79 p ≤ bonus 102 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check148 p, rfl⟩
theorem dir79_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 79 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 79 100 .southWest || decide (bonus 79 p ≤ bonus 100 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check149 p, rfl⟩
theorem dir80_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 .north p = true := by
  rfl
theorem dir80_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 .south p = true := by
  change ((!walkGuard soko2_2.board support p 80 102 .south || decide (bonus 80 p ≤ bonus 102 p)) && ((PreciseRolling.stayTargets soko2_2.board 102 .south).all (fun landing => !pushGuard support p 80 102 124 landing || decide (bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 102 + bonus 102 (change p 102 (some landing)))) && (pushTargets soko2_2.board 102 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 80 102 124 landing || decide (bonus 80 p ≤ 1 - Generated.soko2_2Potential.boulder 102 - Generated.soko2_2Potential.hole landing + bonus 102 (change p 102 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check150 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check151 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir80_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 .east p = true := by
  change ((!walkGuard soko2_2.board support p 80 81 .east || decide (bonus 80 p ≤ bonus 81 p)) && ((PreciseRolling.stayTargets soko2_2.board 81 .east).all (fun landing => !pushGuard support p 80 81 82 landing || decide (bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 81 + bonus 81 (change p 81 (some landing)))) && (pushTargets soko2_2.board 81 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 80 81 82 landing || decide (bonus 80 p ≤ 1 - Generated.soko2_2Potential.boulder 81 - Generated.soko2_2Potential.hole landing + bonus 81 (change p 81 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check152 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check153 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir80_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 .west p = true := by
  change ((!walkGuard soko2_2.board support p 80 79 .west || decide (bonus 80 p ≤ bonus 79 p)) && ((PreciseRolling.stayTargets soko2_2.board 79 .west).all (fun landing => !pushGuard support p 80 79 78 landing || decide (bonus 80 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 79 + bonus 79 (change p 79 (some landing)))) && (pushTargets soko2_2.board 79 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 80 79 78 landing || decide (bonus 80 p ≤ 1 - Generated.soko2_2Potential.boulder 79 - Generated.soko2_2Potential.hole landing + bonus 79 (change p 79 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check154 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check155 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir80_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 .northEast p = true := by
  rfl
theorem dir80_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 .northWest p = true := by
  rfl
theorem dir80_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 80 103 .southEast || decide (bonus 80 p ≤ bonus 103 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check156 p, rfl⟩
theorem dir80_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 80 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 80 101 .southWest || decide (bonus 80 p ≤ bonus 101 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check157 p, rfl⟩
theorem dir81_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 .north p = true := by
  rfl
theorem dir81_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 .south p = true := by
  change ((!walkGuard soko2_2.board support p 81 103 .south || decide (bonus 81 p ≤ bonus 103 p)) && ((PreciseRolling.stayTargets soko2_2.board 103 .south).all (fun landing => !pushGuard support p 81 103 125 landing || decide (bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 103 + bonus 103 (change p 103 (some landing)))) && (pushTargets soko2_2.board 103 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 81 103 125 landing || decide (bonus 81 p ≤ 1 - Generated.soko2_2Potential.boulder 103 - Generated.soko2_2Potential.hole landing + bonus 103 (change p 103 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check158 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check159 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir81_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 .east p = true := by
  change ((!walkGuard soko2_2.board support p 81 82 .east || decide (bonus 81 p ≤ bonus 82 p)) && ((PreciseRolling.stayTargets soko2_2.board 82 .east).all (fun landing => !pushGuard support p 81 82 83 landing || decide (bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 82 + bonus 82 (change p 82 (some landing)))) && (pushTargets soko2_2.board 82 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 81 82 83 landing || decide (bonus 81 p ≤ 1 - Generated.soko2_2Potential.boulder 82 - Generated.soko2_2Potential.hole landing + bonus 82 (change p 82 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check160 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check161 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir81_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 .west p = true := by
  change ((!walkGuard soko2_2.board support p 81 80 .west || decide (bonus 81 p ≤ bonus 80 p)) && ((PreciseRolling.stayTargets soko2_2.board 80 .west).all (fun landing => !pushGuard support p 81 80 79 landing || decide (bonus 81 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 80 + bonus 80 (change p 80 (some landing)))) && (pushTargets soko2_2.board 80 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 81 80 79 landing || decide (bonus 81 p ≤ 1 - Generated.soko2_2Potential.boulder 80 - Generated.soko2_2Potential.hole landing + bonus 80 (change p 80 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check162 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check163 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir81_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 .northEast p = true := by
  rfl
theorem dir81_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 .northWest p = true := by
  rfl
theorem dir81_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 81 104 .southEast || decide (bonus 81 p ≤ bonus 104 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check164 p, rfl⟩
theorem dir81_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 81 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 81 102 .southWest || decide (bonus 81 p ≤ bonus 102 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check165 p, rfl⟩
end NetHack.Sokoban22Refined85
