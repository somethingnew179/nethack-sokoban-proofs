import NetHack.Sokoban22Refined85.Directions12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir162_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 .north p = true := by
  rfl
theorem dir162_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 .south p = true := by
  change ((!walkGuard soko2_2.board support p 162 184 .south || decide (bonus 162 p ≤ bonus 184 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check633 p, rfl⟩
theorem dir162_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 .east p = true := by
  change ((!walkGuard soko2_2.board support p 162 163 .east || decide (bonus 162 p ≤ bonus 163 p)) && ((PreciseRolling.stayTargets soko2_2.board 163 .east).all (fun landing => !pushGuard support p 162 163 164 landing || decide (bonus 162 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some landing)))) && (pushTargets soko2_2.board 163 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 162 163 164 landing || decide (bonus 162 p ≤ 1 - Generated.soko2_2Potential.boulder 163 - Generated.soko2_2Potential.hole landing + bonus 163 (change p 163 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check634 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check635 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir162_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 .west p = true := by
  change ((!walkGuard soko2_2.board support p 162 161 .west || decide (bonus 162 p ≤ bonus 161 p)) && ((PreciseRolling.stayTargets soko2_2.board 161 .west).all (fun landing => !pushGuard support p 162 161 160 landing || decide (bonus 162 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 161 + bonus 161 (change p 161 (some landing)))) && (pushTargets soko2_2.board 161 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 162 161 160 landing || decide (bonus 162 p ≤ 1 - Generated.soko2_2Potential.boulder 161 - Generated.soko2_2Potential.hole landing + bonus 161 (change p 161 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check636 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check637 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir162_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 162 141 .northEast || decide (bonus 162 p ≤ bonus 141 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check638 p, rfl⟩
theorem dir162_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 .northWest p = true := by
  rfl
theorem dir162_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 162 185 .southEast || decide (bonus 162 p ≤ bonus 185 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check639 p, rfl⟩
theorem dir162_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 162 .southWest p = true := by
  rfl
theorem dir163_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 .north p = true := by
  change ((!walkGuard soko2_2.board support p 163 141 .north || decide (bonus 163 p ≤ bonus 141 p)) && ((PreciseRolling.stayTargets soko2_2.board 141 .north).all (fun landing => !pushGuard support p 163 141 119 landing || decide (bonus 163 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 141 + bonus 141 (change p 141 (some landing)))) && (pushTargets soko2_2.board 141 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 163 141 119 landing || decide (bonus 163 p ≤ 1 - Generated.soko2_2Potential.boulder 141 - Generated.soko2_2Potential.hole landing + bonus 141 (change p 141 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check640 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check641 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir163_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 .south p = true := by
  change ((!walkGuard soko2_2.board support p 163 185 .south || decide (bonus 163 p ≤ bonus 185 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check642 p, rfl⟩
theorem dir163_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 .east p = true := by
  change ((!walkGuard soko2_2.board support p 163 164 .east || decide (bonus 163 p ≤ bonus 164 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check643 p, rfl⟩
theorem dir163_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 .west p = true := by
  change ((!walkGuard soko2_2.board support p 163 162 .west || decide (bonus 163 p ≤ bonus 162 p)) && ((PreciseRolling.stayTargets soko2_2.board 162 .west).all (fun landing => !pushGuard support p 163 162 161 landing || decide (bonus 163 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 162 + bonus 162 (change p 162 (some landing)))) && (pushTargets soko2_2.board 162 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 163 162 161 landing || decide (bonus 163 p ≤ 1 - Generated.soko2_2Potential.boulder 162 - Generated.soko2_2Potential.hole landing + bonus 162 (change p 162 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check644 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check645 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir163_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 .northEast p = true := by
  rfl
theorem dir163_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 .northWest p = true := by
  rfl
theorem dir163_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 163 186 .southEast || decide (bonus 163 p ≤ bonus 186 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check646 p, rfl⟩
theorem dir163_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 163 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 163 184 .southWest || decide (bonus 163 p ≤ bonus 184 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check647 p, rfl⟩
theorem dir164_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 .north p = true := by
  rfl
theorem dir164_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 .south p = true := by
  change ((!walkGuard soko2_2.board support p 164 186 .south || decide (bonus 164 p ≤ bonus 186 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check648 p, rfl⟩
theorem dir164_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 .east p = true := by
  rfl
theorem dir164_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 .west p = true := by
  change ((!walkGuard soko2_2.board support p 164 163 .west || decide (bonus 164 p ≤ bonus 163 p)) && ((PreciseRolling.stayTargets soko2_2.board 163 .west).all (fun landing => !pushGuard support p 164 163 162 landing || decide (bonus 164 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some landing)))) && (pushTargets soko2_2.board 163 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 164 163 162 landing || decide (bonus 164 p ≤ 1 - Generated.soko2_2Potential.boulder 163 - Generated.soko2_2Potential.hole landing + bonus 163 (change p 163 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check649 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check650 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir164_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 .northEast p = true := by
  rfl
theorem dir164_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 164 141 .northWest || decide (bonus 164 p ≤ bonus 141 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check651 p, rfl⟩
theorem dir164_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 .southEast p = true := by
  rfl
theorem dir164_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 164 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 164 185 .southWest || decide (bonus 164 p ≤ bonus 185 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check652 p, rfl⟩
theorem dir166_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 .north p = true := by
  change ((!walkGuard soko2_2.board support p 166 144 .north || decide (bonus 166 p ≤ bonus 144 p)) && ((PreciseRolling.stayTargets soko2_2.board 144 .north).all (fun landing => !pushGuard support p 166 144 122 landing || decide (bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 144 + bonus 144 (change p 144 (some landing)))) && (pushTargets soko2_2.board 144 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 166 144 122 landing || decide (bonus 166 p ≤ 1 - Generated.soko2_2Potential.boulder 144 - Generated.soko2_2Potential.hole landing + bonus 144 (change p 144 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check653 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check654 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir166_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 .south p = true := by
  change ((!walkGuard soko2_2.board support p 166 188 .south || decide (bonus 166 p ≤ bonus 188 p)) && ((PreciseRolling.stayTargets soko2_2.board 188 .south).all (fun landing => !pushGuard support p 166 188 210 landing || decide (bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 188 + bonus 188 (change p 188 (some landing)))) && (pushTargets soko2_2.board 188 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 166 188 210 landing || decide (bonus 166 p ≤ 1 - Generated.soko2_2Potential.boulder 188 - Generated.soko2_2Potential.hole landing + bonus 188 (change p 188 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check655 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check656 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir166_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 .east p = true := by
  change ((!walkGuard soko2_2.board support p 166 167 .east || decide (bonus 166 p ≤ bonus 167 p)) && ((PreciseRolling.stayTargets soko2_2.board 167 .east).all (fun landing => !pushGuard support p 166 167 168 landing || decide (bonus 166 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some landing)))) && (pushTargets soko2_2.board 167 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 166 167 168 landing || decide (bonus 166 p ≤ 1 - Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.hole landing + bonus 167 (change p 167 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check657 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check658 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir166_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 .west p = true := by
  rfl
theorem dir166_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 166 145 .northEast || decide (bonus 166 p ≤ bonus 145 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check659 p, rfl⟩
theorem dir166_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 .northWest p = true := by
  rfl
theorem dir166_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 166 189 .southEast || decide (bonus 166 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check660 p, rfl⟩
theorem dir166_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 166 .southWest p = true := by
  rfl
theorem dir167_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 .north p = true := by
  change ((!walkGuard soko2_2.board support p 167 145 .north || decide (bonus 167 p ≤ bonus 145 p)) && ((PreciseRolling.stayTargets soko2_2.board 145 .north).all (fun landing => !pushGuard support p 167 145 123 landing || decide (bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 145 + bonus 145 (change p 145 (some landing)))) && (pushTargets soko2_2.board 145 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 167 145 123 landing || decide (bonus 167 p ≤ 1 - Generated.soko2_2Potential.boulder 145 - Generated.soko2_2Potential.hole landing + bonus 145 (change p 145 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check661 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check662 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir167_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 .south p = true := by
  change ((!walkGuard soko2_2.board support p 167 189 .south || decide (bonus 167 p ≤ bonus 189 p)) && ((PreciseRolling.stayTargets soko2_2.board 189 .south).all (fun landing => !pushGuard support p 167 189 211 landing || decide (bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some landing)))) && (pushTargets soko2_2.board 189 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 167 189 211 landing || decide (bonus 167 p ≤ 1 - Generated.soko2_2Potential.boulder 189 - Generated.soko2_2Potential.hole landing + bonus 189 (change p 189 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check663 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check664 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir167_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 .east p = true := by
  change ((!walkGuard soko2_2.board support p 167 168 .east || decide (bonus 167 p ≤ bonus 168 p)) && ((PreciseRolling.stayTargets soko2_2.board 168 .east).all (fun landing => !pushGuard support p 167 168 169 landing || decide (bonus 167 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some landing)))) && (pushTargets soko2_2.board 168 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 167 168 169 landing || decide (bonus 167 p ≤ 1 - Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.hole landing + bonus 168 (change p 168 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check665 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check666 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir167_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 .west p = true := by
  change ((!walkGuard soko2_2.board support p 167 166 .west || decide (bonus 167 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check667 p, rfl⟩
theorem dir167_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 167 146 .northEast || decide (bonus 167 p ≤ bonus 146 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check668 p, rfl⟩
theorem dir167_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 167 144 .northWest || decide (bonus 167 p ≤ bonus 144 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check669 p, rfl⟩
theorem dir167_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 167 190 .southEast || decide (bonus 167 p ≤ bonus 190 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check670 p, rfl⟩
theorem dir167_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 167 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 167 188 .southWest || decide (bonus 167 p ≤ bonus 188 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check671 p, rfl⟩
theorem dir168_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 .north p = true := by
  change ((!walkGuard soko2_2.board support p 168 146 .north || decide (bonus 168 p ≤ bonus 146 p)) && ((PreciseRolling.stayTargets soko2_2.board 146 .north).all (fun landing => !pushGuard support p 168 146 124 landing || decide (bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 146 + bonus 146 (change p 146 (some landing)))) && (pushTargets soko2_2.board 146 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 168 146 124 landing || decide (bonus 168 p ≤ 1 - Generated.soko2_2Potential.boulder 146 - Generated.soko2_2Potential.hole landing + bonus 146 (change p 146 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check672 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check673 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir168_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 .south p = true := by
  change ((!walkGuard soko2_2.board support p 168 190 .south || decide (bonus 168 p ≤ bonus 190 p)) && ((PreciseRolling.stayTargets soko2_2.board 190 .south).all (fun landing => !pushGuard support p 168 190 212 landing || decide (bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some landing)))) && (pushTargets soko2_2.board 190 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 168 190 212 landing || decide (bonus 168 p ≤ 1 - Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.hole landing + bonus 190 (change p 190 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check674 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check675 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir168_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 .east p = true := by
  change ((!walkGuard soko2_2.board support p 168 169 .east || decide (bonus 168 p ≤ bonus 169 p)) && ((PreciseRolling.stayTargets soko2_2.board 169 .east).all (fun landing => !pushGuard support p 168 169 170 landing || decide (bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some landing)))) && (pushTargets soko2_2.board 169 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 168 169 170 landing || decide (bonus 168 p ≤ 1 - Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.hole landing + bonus 169 (change p 169 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check676 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check677 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir168_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 .west p = true := by
  change ((!walkGuard soko2_2.board support p 168 167 .west || decide (bonus 168 p ≤ bonus 167 p)) && ((PreciseRolling.stayTargets soko2_2.board 167 .west).all (fun landing => !pushGuard support p 168 167 166 landing || decide (bonus 168 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some landing)))) && (pushTargets soko2_2.board 167 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 168 167 166 landing || decide (bonus 168 p ≤ 1 - Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.hole landing + bonus 167 (change p 167 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check678 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check679 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir168_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 168 147 .northEast || decide (bonus 168 p ≤ bonus 147 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check680 p, rfl⟩
theorem dir168_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 168 145 .northWest || decide (bonus 168 p ≤ bonus 145 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check681 p, rfl⟩
theorem dir168_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 168 191 .southEast || decide (bonus 168 p ≤ bonus 191 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check682 p, rfl⟩
theorem dir168_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 168 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 168 189 .southWest || decide (bonus 168 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check683 p, rfl⟩
end NetHack.Sokoban22Refined85
