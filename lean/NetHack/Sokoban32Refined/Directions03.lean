import NetHack.Sokoban32Refined.Directions02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir60_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 .north p = true := by
  rfl
theorem dir60_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 .south p = true := by
  change ((!walkGuard soko3_2.board support p 60 86 .south || decide (bonus 60 p ≤ bonus 86 p)) && ((PreciseRolling.stayTargets soko3_2.board 86 .south).all (fun landing => !pushGuard support p 60 86 112 landing || decide (bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 86 + bonus 86 (change p 86 (some landing)))) && (pushTargets soko3_2.board 86 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 60 86 112 landing || decide (bonus 60 p ≤ 1 - Generated.soko3_2Potential.boulder 86 - Generated.soko3_2Potential.hole landing + bonus 86 (change p 86 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check112 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check113 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir60_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 .east p = true := by
  change ((!walkGuard soko3_2.board support p 60 61 .east || decide (bonus 60 p ≤ bonus 61 p)) && ((PreciseRolling.stayTargets soko3_2.board 61 .east).all (fun landing => !pushGuard support p 60 61 62 landing || decide (bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 61 + bonus 61 (change p 61 (some landing)))) && (pushTargets soko3_2.board 61 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 60 61 62 landing || decide (bonus 60 p ≤ 1 - Generated.soko3_2Potential.boulder 61 - Generated.soko3_2Potential.hole landing + bonus 61 (change p 61 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check114 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check115 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir60_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 .west p = true := by
  change ((!walkGuard soko3_2.board support p 60 59 .west || decide (bonus 60 p ≤ bonus 59 p)) && ((PreciseRolling.stayTargets soko3_2.board 59 .west).all (fun landing => !pushGuard support p 60 59 58 landing || decide (bonus 60 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 59 + bonus 59 (change p 59 (some landing)))) && (pushTargets soko3_2.board 59 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 60 59 58 landing || decide (bonus 60 p ≤ 1 - Generated.soko3_2Potential.boulder 59 - Generated.soko3_2Potential.hole landing + bonus 59 (change p 59 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check116 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check117 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir60_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 .northEast p = true := by
  rfl
theorem dir60_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 .northWest p = true := by
  rfl
theorem dir60_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 .southEast p = true := by
  rfl
theorem dir60_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 60 .southWest p = true := by
  rfl
theorem dir61_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 .north p = true := by
  rfl
theorem dir61_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 .south p = true := by
  rfl
theorem dir61_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 .east p = true := by
  change ((!walkGuard soko3_2.board support p 61 62 .east || decide (bonus 61 p ≤ bonus 62 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check118 p, rfl⟩
theorem dir61_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 .west p = true := by
  change ((!walkGuard soko3_2.board support p 61 60 .west || decide (bonus 61 p ≤ bonus 60 p)) && ((PreciseRolling.stayTargets soko3_2.board 60 .west).all (fun landing => !pushGuard support p 61 60 59 landing || decide (bonus 61 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 60 + bonus 60 (change p 60 (some landing)))) && (pushTargets soko3_2.board 60 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 61 60 59 landing || decide (bonus 61 p ≤ 1 - Generated.soko3_2Potential.boulder 60 - Generated.soko3_2Potential.hole landing + bonus 60 (change p 60 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check119 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check120 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir61_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 .northEast p = true := by
  rfl
theorem dir61_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 .northWest p = true := by
  rfl
theorem dir61_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 61 88 .southEast || decide (bonus 61 p ≤ bonus 88 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check121 p, rfl⟩
theorem dir61_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 61 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 61 86 .southWest || decide (bonus 61 p ≤ bonus 86 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check122 p, rfl⟩
theorem dir62_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 .north p = true := by
  rfl
theorem dir62_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 .south p = true := by
  change ((!walkGuard soko3_2.board support p 62 88 .south || decide (bonus 62 p ≤ bonus 88 p)) && ((PreciseRolling.stayTargets soko3_2.board 88 .south).all (fun landing => !pushGuard support p 62 88 114 landing || decide (bonus 62 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 88 + bonus 88 (change p 88 (some landing)))) && (pushTargets soko3_2.board 88 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 62 88 114 landing || decide (bonus 62 p ≤ 1 - Generated.soko3_2Potential.boulder 88 - Generated.soko3_2Potential.hole landing + bonus 88 (change p 88 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check123 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check124 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir62_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 .east p = true := by
  rfl
theorem dir62_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 .west p = true := by
  change ((!walkGuard soko3_2.board support p 62 61 .west || decide (bonus 62 p ≤ bonus 61 p)) && ((PreciseRolling.stayTargets soko3_2.board 61 .west).all (fun landing => !pushGuard support p 62 61 60 landing || decide (bonus 62 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 61 + bonus 61 (change p 61 (some landing)))) && (pushTargets soko3_2.board 61 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 62 61 60 landing || decide (bonus 62 p ≤ 1 - Generated.soko3_2Potential.boulder 61 - Generated.soko3_2Potential.hole landing + bonus 61 (change p 61 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check125 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check126 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir62_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 .northEast p = true := by
  rfl
theorem dir62_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 .northWest p = true := by
  rfl
theorem dir62_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 .southEast p = true := by
  rfl
theorem dir62_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 62 .southWest p = true := by
  rfl
theorem dir68_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 .north p = true := by
  change ((!walkGuard soko3_2.board support p 68 42 .north || decide (bonus 68 p ≤ bonus 42 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check127 p, rfl⟩
theorem dir68_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 .south p = true := by
  change ((!walkGuard soko3_2.board support p 68 94 .south || decide (bonus 68 p ≤ bonus 94 p)) && ((PreciseRolling.stayTargets soko3_2.board 94 .south).all (fun landing => !pushGuard support p 68 94 120 landing || decide (bonus 68 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 94 + bonus 94 (change p 94 (some landing)))) && (pushTargets soko3_2.board 94 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 68 94 120 landing || decide (bonus 68 p ≤ 1 - Generated.soko3_2Potential.boulder 94 - Generated.soko3_2Potential.hole landing + bonus 94 (change p 94 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check128 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check129 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir68_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 .east p = true := by
  change ((!walkGuard soko3_2.board support p 68 69 .east || decide (bonus 68 p ≤ bonus 69 p)) && ((PreciseRolling.stayTargets soko3_2.board 69 .east).all (fun landing => !pushGuard support p 68 69 70 landing || decide (bonus 68 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some landing)))) && (pushTargets soko3_2.board 69 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 68 69 70 landing || decide (bonus 68 p ≤ 1 - Generated.soko3_2Potential.boulder 69 - Generated.soko3_2Potential.hole landing + bonus 69 (change p 69 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check130 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check131 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir68_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 .west p = true := by
  rfl
theorem dir68_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 68 43 .northEast || decide (bonus 68 p ≤ bonus 43 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check132 p, rfl⟩
theorem dir68_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 .northWest p = true := by
  rfl
theorem dir68_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 68 95 .southEast || decide (bonus 68 p ≤ bonus 95 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check133 p, rfl⟩
theorem dir68_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 68 .southWest p = true := by
  rfl
theorem dir69_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 .north p = true := by
  change ((!walkGuard soko3_2.board support p 69 43 .north || decide (bonus 69 p ≤ bonus 43 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check134 p, rfl⟩
theorem dir69_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 .south p = true := by
  change ((!walkGuard soko3_2.board support p 69 95 .south || decide (bonus 69 p ≤ bonus 95 p)) && ((PreciseRolling.stayTargets soko3_2.board 95 .south).all (fun landing => !pushGuard support p 69 95 121 landing || decide (bonus 69 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 95 + bonus 95 (change p 95 (some landing)))) && (pushTargets soko3_2.board 95 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 69 95 121 landing || decide (bonus 69 p ≤ 1 - Generated.soko3_2Potential.boulder 95 - Generated.soko3_2Potential.hole landing + bonus 95 (change p 95 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check135 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check136 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir69_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 .east p = true := by
  change ((!walkGuard soko3_2.board support p 69 70 .east || decide (bonus 69 p ≤ bonus 70 p)) && ((PreciseRolling.stayTargets soko3_2.board 70 .east).all (fun landing => !pushGuard support p 69 70 71 landing || decide (bonus 69 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 70 + bonus 70 (change p 70 (some landing)))) && (pushTargets soko3_2.board 70 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 69 70 71 landing || decide (bonus 69 p ≤ 1 - Generated.soko3_2Potential.boulder 70 - Generated.soko3_2Potential.hole landing + bonus 70 (change p 70 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check137 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check138 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir69_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 .west p = true := by
  change ((!walkGuard soko3_2.board support p 69 68 .west || decide (bonus 69 p ≤ bonus 68 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check139 p, rfl⟩
theorem dir69_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 69 44 .northEast || decide (bonus 69 p ≤ bonus 44 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check140 p, rfl⟩
theorem dir69_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 69 42 .northWest || decide (bonus 69 p ≤ bonus 42 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check141 p, rfl⟩
theorem dir69_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 69 96 .southEast || decide (bonus 69 p ≤ bonus 96 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check142 p, rfl⟩
theorem dir69_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 69 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 69 94 .southWest || decide (bonus 69 p ≤ bonus 94 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check143 p, rfl⟩
theorem dir70_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 .north p = true := by
  change ((!walkGuard soko3_2.board support p 70 44 .north || decide (bonus 70 p ≤ bonus 44 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check144 p, rfl⟩
theorem dir70_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 .south p = true := by
  change ((!walkGuard soko3_2.board support p 70 96 .south || decide (bonus 70 p ≤ bonus 96 p)) && ((PreciseRolling.stayTargets soko3_2.board 96 .south).all (fun landing => !pushGuard support p 70 96 122 landing || decide (bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 96 + bonus 96 (change p 96 (some landing)))) && (pushTargets soko3_2.board 96 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 70 96 122 landing || decide (bonus 70 p ≤ 1 - Generated.soko3_2Potential.boulder 96 - Generated.soko3_2Potential.hole landing + bonus 96 (change p 96 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check145 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check146 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir70_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 .east p = true := by
  change ((!walkGuard soko3_2.board support p 70 71 .east || decide (bonus 70 p ≤ bonus 71 p)) && ((PreciseRolling.stayTargets soko3_2.board 71 .east).all (fun landing => !pushGuard support p 70 71 72 landing || decide (bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 71 + bonus 71 (change p 71 (some landing)))) && (pushTargets soko3_2.board 71 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 70 71 72 landing || decide (bonus 70 p ≤ 1 - Generated.soko3_2Potential.boulder 71 - Generated.soko3_2Potential.hole landing + bonus 71 (change p 71 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check147 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check148 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir70_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 .west p = true := by
  change ((!walkGuard soko3_2.board support p 70 69 .west || decide (bonus 70 p ≤ bonus 69 p)) && ((PreciseRolling.stayTargets soko3_2.board 69 .west).all (fun landing => !pushGuard support p 70 69 68 landing || decide (bonus 70 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 69 + bonus 69 (change p 69 (some landing)))) && (pushTargets soko3_2.board 69 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 70 69 68 landing || decide (bonus 70 p ≤ 1 - Generated.soko3_2Potential.boulder 69 - Generated.soko3_2Potential.hole landing + bonus 69 (change p 69 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check149 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check150 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir70_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 70 45 .northEast || decide (bonus 70 p ≤ bonus 45 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check151 p, rfl⟩
theorem dir70_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 70 43 .northWest || decide (bonus 70 p ≤ bonus 43 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check152 p, rfl⟩
theorem dir70_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 70 97 .southEast || decide (bonus 70 p ≤ bonus 97 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check153 p, rfl⟩
theorem dir70_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 70 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 70 95 .southWest || decide (bonus 70 p ≤ bonus 95 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check154 p, rfl⟩
end NetHack.Sokoban32Refined
