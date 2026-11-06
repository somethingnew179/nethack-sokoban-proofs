import NetHack.Sokoban32Refined.Directions13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir163_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 .north p = true := by
  change ((!walkGuard soko3_2.board support p 163 137 .north || decide (bonus 163 p ≤ bonus 137 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check714 p, rfl⟩
theorem dir163_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 .south p = true := by
  change ((!walkGuard soko3_2.board support p 163 189 .south || decide (bonus 163 p ≤ bonus 189 p)) && ((PreciseRolling.stayTargets soko3_2.board 189 .south).all (fun landing => !pushGuard support p 163 189 215 landing || decide (bonus 163 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 189 + bonus 189 (change p 189 (some landing)))) && (pushTargets soko3_2.board 189 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 163 189 215 landing || decide (bonus 163 p ≤ 1 - Generated.soko3_2Potential.boulder 189 - Generated.soko3_2Potential.hole landing + bonus 189 (change p 189 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check715 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check716 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir163_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 .east p = true := by
  rfl
theorem dir163_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 .west p = true := by
  change ((!walkGuard soko3_2.board support p 163 162 .west || decide (bonus 163 p ≤ bonus 162 p)) && ((PreciseRolling.stayTargets soko3_2.board 162 .west).all (fun landing => !pushGuard support p 163 162 161 landing || decide (bonus 163 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some landing)))) && (pushTargets soko3_2.board 162 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 163 162 161 landing || decide (bonus 163 p ≤ 1 - Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.hole landing + bonus 162 (change p 162 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check717 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check718 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir163_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 163 138 .northEast || decide (bonus 163 p ≤ bonus 138 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check719 p, rfl⟩
theorem dir163_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 163 136 .northWest || decide (bonus 163 p ≤ bonus 136 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check720 p, rfl⟩
theorem dir163_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 .southEast p = true := by
  rfl
theorem dir163_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 163 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 163 188 .southWest || decide (bonus 163 p ≤ bonus 188 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check721 p, rfl⟩
theorem dir165_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 .north p = true := by
  change ((!walkGuard soko3_2.board support p 165 139 .north || decide (bonus 165 p ≤ bonus 139 p)) && ((PreciseRolling.stayTargets soko3_2.board 139 .north).all (fun landing => !pushGuard support p 165 139 113 landing || decide (bonus 165 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 139 + bonus 139 (change p 139 (some landing)))) && (pushTargets soko3_2.board 139 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 165 139 113 landing || decide (bonus 165 p ≤ 1 - Generated.soko3_2Potential.boulder 139 - Generated.soko3_2Potential.hole landing + bonus 139 (change p 139 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check722 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check723 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir165_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 .south p = true := by
  rfl
theorem dir165_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 .east p = true := by
  change ((!walkGuard soko3_2.board support p 165 166 .east || decide (bonus 165 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check724 p, rfl⟩
theorem dir165_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 .west p = true := by
  rfl
theorem dir165_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 .northEast p = true := by
  rfl
theorem dir165_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 165 138 .northWest || decide (bonus 165 p ≤ bonus 138 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check725 p, rfl⟩
theorem dir165_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 165 192 .southEast || decide (bonus 165 p ≤ bonus 192 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check726 p, rfl⟩
theorem dir165_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 165 .southWest p = true := by
  rfl
theorem dir166_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 .north p = true := by
  rfl
theorem dir166_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 .south p = true := by
  change ((!walkGuard soko3_2.board support p 166 192 .south || decide (bonus 166 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko3_2.board 192 .south).all (fun landing => !pushGuard support p 166 192 218 landing || decide (bonus 166 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko3_2.board 192 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 166 192 218 landing || decide (bonus 166 p ≤ 1 - Generated.soko3_2Potential.boulder 192 - Generated.soko3_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check727 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check728 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir166_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 .east p = true := by
  rfl
theorem dir166_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 .west p = true := by
  change ((!walkGuard soko3_2.board support p 166 165 .west || decide (bonus 166 p ≤ bonus 165 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check729 p, rfl⟩
theorem dir166_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 .northEast p = true := by
  rfl
theorem dir166_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 166 139 .northWest || decide (bonus 166 p ≤ bonus 139 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check730 p, rfl⟩
theorem dir166_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 .southEast p = true := by
  rfl
theorem dir166_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 166 .southWest p = true := by
  rfl
theorem dir172_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 .north p = true := by
  change ((!walkGuard soko3_2.board support p 172 146 .north || decide (bonus 172 p ≤ bonus 146 p)) && ((PreciseRolling.stayTargets soko3_2.board 146 .north).all (fun landing => !pushGuard support p 172 146 120 landing || decide (bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 146 + bonus 146 (change p 146 (some landing)))) && (pushTargets soko3_2.board 146 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 172 146 120 landing || decide (bonus 172 p ≤ 1 - Generated.soko3_2Potential.boulder 146 - Generated.soko3_2Potential.hole landing + bonus 146 (change p 146 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check731 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check732 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir172_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 .south p = true := by
  change ((!walkGuard soko3_2.board support p 172 198 .south || decide (bonus 172 p ≤ bonus 198 p)) && ((PreciseRolling.stayTargets soko3_2.board 198 .south).all (fun landing => !pushGuard support p 172 198 224 landing || decide (bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 198 + bonus 198 (change p 198 (some landing)))) && (pushTargets soko3_2.board 198 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 172 198 224 landing || decide (bonus 172 p ≤ 1 - Generated.soko3_2Potential.boulder 198 - Generated.soko3_2Potential.hole landing + bonus 198 (change p 198 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check733 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check734 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir172_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 .east p = true := by
  change ((!walkGuard soko3_2.board support p 172 173 .east || decide (bonus 172 p ≤ bonus 173 p)) && ((PreciseRolling.stayTargets soko3_2.board 173 .east).all (fun landing => !pushGuard support p 172 173 174 landing || decide (bonus 172 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some landing)))) && (pushTargets soko3_2.board 173 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 172 173 174 landing || decide (bonus 172 p ≤ 1 - Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.hole landing + bonus 173 (change p 173 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check735 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check736 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir172_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 .west p = true := by
  rfl
theorem dir172_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 172 147 .northEast || decide (bonus 172 p ≤ bonus 147 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check737 p, rfl⟩
theorem dir172_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 .northWest p = true := by
  rfl
theorem dir172_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 172 199 .southEast || decide (bonus 172 p ≤ bonus 199 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check738 p, rfl⟩
theorem dir172_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 172 .southWest p = true := by
  rfl
theorem dir173_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 .north p = true := by
  change ((!walkGuard soko3_2.board support p 173 147 .north || decide (bonus 173 p ≤ bonus 147 p)) && ((PreciseRolling.stayTargets soko3_2.board 147 .north).all (fun landing => !pushGuard support p 173 147 121 landing || decide (bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 147 + bonus 147 (change p 147 (some landing)))) && (pushTargets soko3_2.board 147 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 173 147 121 landing || decide (bonus 173 p ≤ 1 - Generated.soko3_2Potential.boulder 147 - Generated.soko3_2Potential.hole landing + bonus 147 (change p 147 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check739 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check740 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir173_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 .south p = true := by
  change ((!walkGuard soko3_2.board support p 173 199 .south || decide (bonus 173 p ≤ bonus 199 p)) && ((PreciseRolling.stayTargets soko3_2.board 199 .south).all (fun landing => !pushGuard support p 173 199 225 landing || decide (bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some landing)))) && (pushTargets soko3_2.board 199 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 173 199 225 landing || decide (bonus 173 p ≤ 1 - Generated.soko3_2Potential.boulder 199 - Generated.soko3_2Potential.hole landing + bonus 199 (change p 199 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check741 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check742 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir173_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 .east p = true := by
  change ((!walkGuard soko3_2.board support p 173 174 .east || decide (bonus 173 p ≤ bonus 174 p)) && ((PreciseRolling.stayTargets soko3_2.board 174 .east).all (fun landing => !pushGuard support p 173 174 175 landing || decide (bonus 173 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some landing)))) && (pushTargets soko3_2.board 174 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 173 174 175 landing || decide (bonus 173 p ≤ 1 - Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.hole landing + bonus 174 (change p 174 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check743 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check744 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir173_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 .west p = true := by
  change ((!walkGuard soko3_2.board support p 173 172 .west || decide (bonus 173 p ≤ bonus 172 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check745 p, rfl⟩
theorem dir173_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 173 148 .northEast || decide (bonus 173 p ≤ bonus 148 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check746 p, rfl⟩
theorem dir173_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 173 146 .northWest || decide (bonus 173 p ≤ bonus 146 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check747 p, rfl⟩
theorem dir173_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 173 200 .southEast || decide (bonus 173 p ≤ bonus 200 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check748 p, rfl⟩
theorem dir173_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 173 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 173 198 .southWest || decide (bonus 173 p ≤ bonus 198 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check749 p, rfl⟩
theorem dir174_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 .north p = true := by
  change ((!walkGuard soko3_2.board support p 174 148 .north || decide (bonus 174 p ≤ bonus 148 p)) && ((PreciseRolling.stayTargets soko3_2.board 148 .north).all (fun landing => !pushGuard support p 174 148 122 landing || decide (bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 148 + bonus 148 (change p 148 (some landing)))) && (pushTargets soko3_2.board 148 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 174 148 122 landing || decide (bonus 174 p ≤ 1 - Generated.soko3_2Potential.boulder 148 - Generated.soko3_2Potential.hole landing + bonus 148 (change p 148 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check750 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check751 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir174_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 .south p = true := by
  change ((!walkGuard soko3_2.board support p 174 200 .south || decide (bonus 174 p ≤ bonus 200 p)) && ((PreciseRolling.stayTargets soko3_2.board 200 .south).all (fun landing => !pushGuard support p 174 200 226 landing || decide (bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some landing)))) && (pushTargets soko3_2.board 200 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 174 200 226 landing || decide (bonus 174 p ≤ 1 - Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.hole landing + bonus 200 (change p 200 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check752 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check753 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir174_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 .east p = true := by
  change ((!walkGuard soko3_2.board support p 174 175 .east || decide (bonus 174 p ≤ bonus 175 p)) && ((PreciseRolling.stayTargets soko3_2.board 175 .east).all (fun landing => !pushGuard support p 174 175 176 landing || decide (bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some landing)))) && (pushTargets soko3_2.board 175 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 174 175 176 landing || decide (bonus 174 p ≤ 1 - Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.hole landing + bonus 175 (change p 175 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check754 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check755 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir174_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 .west p = true := by
  change ((!walkGuard soko3_2.board support p 174 173 .west || decide (bonus 174 p ≤ bonus 173 p)) && ((PreciseRolling.stayTargets soko3_2.board 173 .west).all (fun landing => !pushGuard support p 174 173 172 landing || decide (bonus 174 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some landing)))) && (pushTargets soko3_2.board 173 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 174 173 172 landing || decide (bonus 174 p ≤ 1 - Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.hole landing + bonus 173 (change p 173 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check756 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check757 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir174_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 174 149 .northEast || decide (bonus 174 p ≤ bonus 149 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check758 p, rfl⟩
theorem dir174_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 174 147 .northWest || decide (bonus 174 p ≤ bonus 147 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check759 p, rfl⟩
theorem dir174_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 174 201 .southEast || decide (bonus 174 p ≤ bonus 201 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check760 p, rfl⟩
theorem dir174_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 174 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 174 199 .southWest || decide (bonus 174 p ≤ bonus 199 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check761 p, rfl⟩
end NetHack.Sokoban32Refined
