import NetHack.Sokoban22Refined85.Directions01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir52_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 .north p = true := by
  change ((!walkGuard soko2_2.board support p 52 30 .north || decide (bonus 52 p ≤ bonus 30 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check82 p, rfl⟩
theorem dir52_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 .south p = true := by
  change ((!walkGuard soko2_2.board support p 52 74 .south || decide (bonus 52 p ≤ bonus 74 p)) && ((PreciseRolling.stayTargets soko2_2.board 74 .south).all (fun landing => !pushGuard support p 52 74 96 landing || decide (bonus 52 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 74 + bonus 74 (change p 74 (some landing)))) && (pushTargets soko2_2.board 74 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 52 74 96 landing || decide (bonus 52 p ≤ 1 - Generated.soko2_2Potential.boulder 74 - Generated.soko2_2Potential.hole landing + bonus 74 (change p 74 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check83 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check84 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir52_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 .east p = true := by
  rfl
theorem dir52_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 .west p = true := by
  change ((!walkGuard soko2_2.board support p 52 51 .west || decide (bonus 52 p ≤ bonus 51 p)) && ((PreciseRolling.stayTargets soko2_2.board 51 .west).all (fun landing => !pushGuard support p 52 51 50 landing || decide (bonus 52 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some landing)))) && (pushTargets soko2_2.board 51 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 52 51 50 landing || decide (bonus 52 p ≤ 1 - Generated.soko2_2Potential.boulder 51 - Generated.soko2_2Potential.hole landing + bonus 51 (change p 51 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check85 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check86 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir52_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 .northEast p = true := by
  rfl
theorem dir52_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 52 29 .northWest || decide (bonus 52 p ≤ bonus 29 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check87 p, rfl⟩
theorem dir52_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 .southEast p = true := by
  rfl
theorem dir52_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 52 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 52 73 .southWest || decide (bonus 52 p ≤ bonus 73 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check88 p, rfl⟩
theorem dir67_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 .north p = true := by
  change ((!walkGuard soko2_2.board support p 67 45 .north || decide (bonus 67 p ≤ bonus 45 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check89 p, rfl⟩
theorem dir67_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 .south p = true := by
  change ((!walkGuard soko2_2.board support p 67 89 .south || decide (bonus 67 p ≤ bonus 89 p)) && ((PreciseRolling.stayTargets soko2_2.board 89 .south).all (fun landing => !pushGuard support p 67 89 111 landing || decide (bonus 67 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 89 + bonus 89 (change p 89 (some landing)))) && (pushTargets soko2_2.board 89 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 67 89 111 landing || decide (bonus 67 p ≤ 1 - Generated.soko2_2Potential.boulder 89 - Generated.soko2_2Potential.hole landing + bonus 89 (change p 89 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check90 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check91 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir67_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 .east p = true := by
  rfl
theorem dir67_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 .west p = true := by
  rfl
theorem dir67_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 67 46 .northEast || decide (bonus 67 p ≤ bonus 46 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check92 p, rfl⟩
theorem dir67_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 .northWest p = true := by
  rfl
theorem dir67_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 67 90 .southEast || decide (bonus 67 p ≤ bonus 90 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check93 p, rfl⟩
theorem dir67_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 67 .southWest p = true := by
  rfl
theorem dir69_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 .north p = true := by
  change ((!walkGuard soko2_2.board support p 69 47 .north || decide (bonus 69 p ≤ bonus 47 p)) && ((PreciseRolling.stayTargets soko2_2.board 47 .north).all (fun landing => !pushGuard support p 69 47 25 landing || decide (bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 47 + bonus 47 (change p 47 (some landing)))) && (pushTargets soko2_2.board 47 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 69 47 25 landing || decide (bonus 69 p ≤ 1 - Generated.soko2_2Potential.boulder 47 - Generated.soko2_2Potential.hole landing + bonus 47 (change p 47 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check94 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check95 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir69_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 .south p = true := by
  change ((!walkGuard soko2_2.board support p 69 91 .south || decide (bonus 69 p ≤ bonus 91 p)) && ((PreciseRolling.stayTargets soko2_2.board 91 .south).all (fun landing => !pushGuard support p 69 91 113 landing || decide (bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 91 + bonus 91 (change p 91 (some landing)))) && (pushTargets soko2_2.board 91 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 69 91 113 landing || decide (bonus 69 p ≤ 1 - Generated.soko2_2Potential.boulder 91 - Generated.soko2_2Potential.hole landing + bonus 91 (change p 91 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check96 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check97 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir69_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 .east p = true := by
  change ((!walkGuard soko2_2.board support p 69 70 .east || decide (bonus 69 p ≤ bonus 70 p)) && ((PreciseRolling.stayTargets soko2_2.board 70 .east).all (fun landing => !pushGuard support p 69 70 71 landing || decide (bonus 69 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 70 + bonus 70 (change p 70 (some landing)))) && (pushTargets soko2_2.board 70 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 69 70 71 landing || decide (bonus 69 p ≤ 1 - Generated.soko2_2Potential.boulder 70 - Generated.soko2_2Potential.hole landing + bonus 70 (change p 70 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check98 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check99 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir69_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 .west p = true := by
  rfl
theorem dir69_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 69 48 .northEast || decide (bonus 69 p ≤ bonus 48 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check100 p, rfl⟩
theorem dir69_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 69 46 .northWest || decide (bonus 69 p ≤ bonus 46 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check101 p, rfl⟩
theorem dir69_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 .southEast p = true := by
  rfl
theorem dir69_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 69 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 69 90 .southWest || decide (bonus 69 p ≤ bonus 90 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check102 p, rfl⟩
theorem dir70_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 .north p = true := by
  change ((!walkGuard soko2_2.board support p 70 48 .north || decide (bonus 70 p ≤ bonus 48 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check103 p, rfl⟩
theorem dir70_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 .south p = true := by
  rfl
theorem dir70_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 .east p = true := by
  change ((!walkGuard soko2_2.board support p 70 71 .east || decide (bonus 70 p ≤ bonus 71 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check104 p, rfl⟩
theorem dir70_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 .west p = true := by
  change ((!walkGuard soko2_2.board support p 70 69 .west || decide (bonus 70 p ≤ bonus 69 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check105 p, rfl⟩
theorem dir70_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 70 49 .northEast || decide (bonus 70 p ≤ bonus 49 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check106 p, rfl⟩
theorem dir70_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 70 47 .northWest || decide (bonus 70 p ≤ bonus 47 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check107 p, rfl⟩
theorem dir70_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 70 93 .southEast || decide (bonus 70 p ≤ bonus 93 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check108 p, rfl⟩
theorem dir70_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 70 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 70 91 .southWest || decide (bonus 70 p ≤ bonus 91 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check109 p, rfl⟩
theorem dir71_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 .north p = true := by
  change ((!walkGuard soko2_2.board support p 71 49 .north || decide (bonus 71 p ≤ bonus 49 p)) && ((PreciseRolling.stayTargets soko2_2.board 49 .north).all (fun landing => !pushGuard support p 71 49 27 landing || decide (bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 49 + bonus 49 (change p 49 (some landing)))) && (pushTargets soko2_2.board 49 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 71 49 27 landing || decide (bonus 71 p ≤ 1 - Generated.soko2_2Potential.boulder 49 - Generated.soko2_2Potential.hole landing + bonus 49 (change p 49 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check110 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check111 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir71_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 .south p = true := by
  change ((!walkGuard soko2_2.board support p 71 93 .south || decide (bonus 71 p ≤ bonus 93 p)) && ((PreciseRolling.stayTargets soko2_2.board 93 .south).all (fun landing => !pushGuard support p 71 93 115 landing || decide (bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 93 + bonus 93 (change p 93 (some landing)))) && (pushTargets soko2_2.board 93 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 71 93 115 landing || decide (bonus 71 p ≤ 1 - Generated.soko2_2Potential.boulder 93 - Generated.soko2_2Potential.hole landing + bonus 93 (change p 93 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check112 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check113 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir71_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 .east p = true := by
  rfl
theorem dir71_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 .west p = true := by
  change ((!walkGuard soko2_2.board support p 71 70 .west || decide (bonus 71 p ≤ bonus 70 p)) && ((PreciseRolling.stayTargets soko2_2.board 70 .west).all (fun landing => !pushGuard support p 71 70 69 landing || decide (bonus 71 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 70 + bonus 70 (change p 70 (some landing)))) && (pushTargets soko2_2.board 70 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 71 70 69 landing || decide (bonus 71 p ≤ 1 - Generated.soko2_2Potential.boulder 70 - Generated.soko2_2Potential.hole landing + bonus 70 (change p 70 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check114 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check115 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir71_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 71 50 .northEast || decide (bonus 71 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check116 p, rfl⟩
theorem dir71_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 71 48 .northWest || decide (bonus 71 p ≤ bonus 48 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check117 p, rfl⟩
theorem dir71_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 71 94 .southEast || decide (bonus 71 p ≤ bonus 94 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check118 p, rfl⟩
theorem dir71_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 71 .southWest p = true := by
  rfl
theorem dir73_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 .north p = true := by
  change ((!walkGuard soko2_2.board support p 73 51 .north || decide (bonus 73 p ≤ bonus 51 p)) && ((PreciseRolling.stayTargets soko2_2.board 51 .north).all (fun landing => !pushGuard support p 73 51 29 landing || decide (bonus 73 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 51 + bonus 51 (change p 51 (some landing)))) && (pushTargets soko2_2.board 51 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 73 51 29 landing || decide (bonus 73 p ≤ 1 - Generated.soko2_2Potential.boulder 51 - Generated.soko2_2Potential.hole landing + bonus 51 (change p 51 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check119 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check120 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir73_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 .south p = true := by
  change ((!walkGuard soko2_2.board support p 73 95 .south || decide (bonus 73 p ≤ bonus 95 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check121 p, rfl⟩
theorem dir73_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 .east p = true := by
  change ((!walkGuard soko2_2.board support p 73 74 .east || decide (bonus 73 p ≤ bonus 74 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check122 p, rfl⟩
theorem dir73_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 .west p = true := by
  rfl
theorem dir73_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 73 52 .northEast || decide (bonus 73 p ≤ bonus 52 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check123 p, rfl⟩
theorem dir73_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 73 50 .northWest || decide (bonus 73 p ≤ bonus 50 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check124 p, rfl⟩
theorem dir73_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 73 96 .southEast || decide (bonus 73 p ≤ bonus 96 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check125 p, rfl⟩
theorem dir73_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 73 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 73 94 .southWest || decide (bonus 73 p ≤ bonus 94 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check126 p, rfl⟩
end NetHack.Sokoban22Refined85
