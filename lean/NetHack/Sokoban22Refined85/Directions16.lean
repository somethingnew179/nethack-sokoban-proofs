import NetHack.Sokoban22Refined85.Directions15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir189_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 .north p = true := by
  change ((!walkGuard soko2_2.board support p 189 167 .north || decide (bonus 189 p ≤ bonus 167 p)) && ((PreciseRolling.stayTargets soko2_2.board 167 .north).all (fun landing => !pushGuard support p 189 167 145 landing || decide (bonus 189 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 167 + bonus 167 (change p 167 (some landing)))) && (pushTargets soko2_2.board 167 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 189 167 145 landing || decide (bonus 189 p ≤ 1 - Generated.soko2_2Potential.boulder 167 - Generated.soko2_2Potential.hole landing + bonus 167 (change p 167 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check778 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check779 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir189_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 .south p = true := by
  change ((!walkGuard soko2_2.board support p 189 211 .south || decide (bonus 189 p ≤ bonus 211 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check780 p, rfl⟩
theorem dir189_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 .east p = true := by
  change ((!walkGuard soko2_2.board support p 189 190 .east || decide (bonus 189 p ≤ bonus 190 p)) && ((PreciseRolling.stayTargets soko2_2.board 190 .east).all (fun landing => !pushGuard support p 189 190 191 landing || decide (bonus 189 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some landing)))) && (pushTargets soko2_2.board 190 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 189 190 191 landing || decide (bonus 189 p ≤ 1 - Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.hole landing + bonus 190 (change p 190 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check781 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check782 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir189_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 .west p = true := by
  change ((!walkGuard soko2_2.board support p 189 188 .west || decide (bonus 189 p ≤ bonus 188 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check783 p, rfl⟩
theorem dir189_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 189 168 .northEast || decide (bonus 189 p ≤ bonus 168 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check784 p, rfl⟩
theorem dir189_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 189 166 .northWest || decide (bonus 189 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check785 p, rfl⟩
theorem dir189_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 189 212 .southEast || decide (bonus 189 p ≤ bonus 212 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check786 p, rfl⟩
theorem dir189_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 189 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 189 210 .southWest || decide (bonus 189 p ≤ bonus 210 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check787 p, rfl⟩
theorem dir190_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 .north p = true := by
  change ((!walkGuard soko2_2.board support p 190 168 .north || decide (bonus 190 p ≤ bonus 168 p)) && ((PreciseRolling.stayTargets soko2_2.board 168 .north).all (fun landing => !pushGuard support p 190 168 146 landing || decide (bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 168 + bonus 168 (change p 168 (some landing)))) && (pushTargets soko2_2.board 168 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 190 168 146 landing || decide (bonus 190 p ≤ 1 - Generated.soko2_2Potential.boulder 168 - Generated.soko2_2Potential.hole landing + bonus 168 (change p 168 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check788 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check789 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir190_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 .south p = true := by
  change ((!walkGuard soko2_2.board support p 190 212 .south || decide (bonus 190 p ≤ bonus 212 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check790 p, rfl⟩
theorem dir190_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 .east p = true := by
  change ((!walkGuard soko2_2.board support p 190 191 .east || decide (bonus 190 p ≤ bonus 191 p)) && ((PreciseRolling.stayTargets soko2_2.board 191 .east).all (fun landing => !pushGuard support p 190 191 192 landing || decide (bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some landing)))) && (pushTargets soko2_2.board 191 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 190 191 192 landing || decide (bonus 190 p ≤ 1 - Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.hole landing + bonus 191 (change p 191 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check791 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check792 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir190_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 .west p = true := by
  change ((!walkGuard soko2_2.board support p 190 189 .west || decide (bonus 190 p ≤ bonus 189 p)) && ((PreciseRolling.stayTargets soko2_2.board 189 .west).all (fun landing => !pushGuard support p 190 189 188 landing || decide (bonus 190 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some landing)))) && (pushTargets soko2_2.board 189 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 190 189 188 landing || decide (bonus 190 p ≤ 1 - Generated.soko2_2Potential.boulder 189 - Generated.soko2_2Potential.hole landing + bonus 189 (change p 189 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check793 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check794 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir190_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 190 169 .northEast || decide (bonus 190 p ≤ bonus 169 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check795 p, rfl⟩
theorem dir190_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 190 167 .northWest || decide (bonus 190 p ≤ bonus 167 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check796 p, rfl⟩
theorem dir190_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 190 213 .southEast || decide (bonus 190 p ≤ bonus 213 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check797 p, rfl⟩
theorem dir190_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 190 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 190 211 .southWest || decide (bonus 190 p ≤ bonus 211 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check798 p, rfl⟩
theorem dir191_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 .north p = true := by
  change ((!walkGuard soko2_2.board support p 191 169 .north || decide (bonus 191 p ≤ bonus 169 p)) && ((PreciseRolling.stayTargets soko2_2.board 169 .north).all (fun landing => !pushGuard support p 191 169 147 landing || decide (bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 169 + bonus 169 (change p 169 (some landing)))) && (pushTargets soko2_2.board 169 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 191 169 147 landing || decide (bonus 191 p ≤ 1 - Generated.soko2_2Potential.boulder 169 - Generated.soko2_2Potential.hole landing + bonus 169 (change p 169 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check799 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check800 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir191_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 .south p = true := by
  change ((!walkGuard soko2_2.board support p 191 213 .south || decide (bonus 191 p ≤ bonus 213 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check801 p, rfl⟩
theorem dir191_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 .east p = true := by
  change ((!walkGuard soko2_2.board support p 191 192 .east || decide (bonus 191 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko2_2.board 192 .east).all (fun landing => !pushGuard support p 191 192 193 landing || decide (bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko2_2.board 192 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 191 192 193 landing || decide (bonus 191 p ≤ 1 - Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check802 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check803 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir191_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 .west p = true := by
  change ((!walkGuard soko2_2.board support p 191 190 .west || decide (bonus 191 p ≤ bonus 190 p)) && ((PreciseRolling.stayTargets soko2_2.board 190 .west).all (fun landing => !pushGuard support p 191 190 189 landing || decide (bonus 191 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some landing)))) && (pushTargets soko2_2.board 190 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 191 190 189 landing || decide (bonus 191 p ≤ 1 - Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.hole landing + bonus 190 (change p 190 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check804 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check805 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir191_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 191 170 .northEast || decide (bonus 191 p ≤ bonus 170 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check806 p, rfl⟩
theorem dir191_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 191 168 .northWest || decide (bonus 191 p ≤ bonus 168 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check807 p, rfl⟩
theorem dir191_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 191 214 .southEast || decide (bonus 191 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check808 p, rfl⟩
theorem dir191_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 191 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 191 212 .southWest || decide (bonus 191 p ≤ bonus 212 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check809 p, rfl⟩
theorem dir192_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 .north p = true := by
  change ((!walkGuard soko2_2.board support p 192 170 .north || decide (bonus 192 p ≤ bonus 170 p)) && ((PreciseRolling.stayTargets soko2_2.board 170 .north).all (fun landing => !pushGuard support p 192 170 148 landing || decide (bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 170 + bonus 170 (change p 170 (some landing)))) && (pushTargets soko2_2.board 170 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 192 170 148 landing || decide (bonus 192 p ≤ 1 - Generated.soko2_2Potential.boulder 170 - Generated.soko2_2Potential.hole landing + bonus 170 (change p 170 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check810 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check811 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir192_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 .south p = true := by
  change ((!walkGuard soko2_2.board support p 192 214 .south || decide (bonus 192 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check812 p, rfl⟩
theorem dir192_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 .east p = true := by
  change ((!walkGuard soko2_2.board support p 192 193 .east || decide (bonus 192 p ≤ bonus 193 p)) && ((PreciseRolling.stayTargets soko2_2.board 193 .east).all (fun landing => !pushGuard support p 192 193 194 landing || decide (bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some landing)))) && (pushTargets soko2_2.board 193 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 192 193 194 landing || decide (bonus 192 p ≤ 1 - Generated.soko2_2Potential.boulder 193 - Generated.soko2_2Potential.hole landing + bonus 193 (change p 193 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check813 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check814 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir192_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 .west p = true := by
  change ((!walkGuard soko2_2.board support p 192 191 .west || decide (bonus 192 p ≤ bonus 191 p)) && ((PreciseRolling.stayTargets soko2_2.board 191 .west).all (fun landing => !pushGuard support p 192 191 190 landing || decide (bonus 192 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some landing)))) && (pushTargets soko2_2.board 191 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 192 191 190 landing || decide (bonus 192 p ≤ 1 - Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.hole landing + bonus 191 (change p 191 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check815 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check816 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir192_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 192 171 .northEast || decide (bonus 192 p ≤ bonus 171 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check817 p, rfl⟩
theorem dir192_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 192 169 .northWest || decide (bonus 192 p ≤ bonus 169 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check818 p, rfl⟩
theorem dir192_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 192 215 .southEast || decide (bonus 192 p ≤ bonus 215 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check819 p, rfl⟩
theorem dir192_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 192 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 192 213 .southWest || decide (bonus 192 p ≤ bonus 213 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check820 p, rfl⟩
theorem dir193_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 .north p = true := by
  change ((!walkGuard soko2_2.board support p 193 171 .north || decide (bonus 193 p ≤ bonus 171 p)) && ((PreciseRolling.stayTargets soko2_2.board 171 .north).all (fun landing => !pushGuard support p 193 171 149 landing || decide (bonus 193 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 171 + bonus 171 (change p 171 (some landing)))) && (pushTargets soko2_2.board 171 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 193 171 149 landing || decide (bonus 193 p ≤ 1 - Generated.soko2_2Potential.boulder 171 - Generated.soko2_2Potential.hole landing + bonus 171 (change p 171 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check821 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check822 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir193_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 .south p = true := by
  change ((!walkGuard soko2_2.board support p 193 215 .south || decide (bonus 193 p ≤ bonus 215 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check823 p, rfl⟩
theorem dir193_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 .east p = true := by
  change ((!walkGuard soko2_2.board support p 193 194 .east || decide (bonus 193 p ≤ bonus 194 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check824 p, rfl⟩
theorem dir193_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 .west p = true := by
  change ((!walkGuard soko2_2.board support p 193 192 .west || decide (bonus 193 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko2_2.board 192 .west).all (fun landing => !pushGuard support p 193 192 191 landing || decide (bonus 193 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko2_2.board 192 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 193 192 191 landing || decide (bonus 193 p ≤ 1 - Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check825 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check826 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir193_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 193 172 .northEast || decide (bonus 193 p ≤ bonus 172 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check827 p, rfl⟩
theorem dir193_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 193 170 .northWest || decide (bonus 193 p ≤ bonus 170 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check828 p, rfl⟩
theorem dir193_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 193 216 .southEast || decide (bonus 193 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check829 p, rfl⟩
theorem dir193_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 193 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 193 214 .southWest || decide (bonus 193 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check830 p, rfl⟩
theorem dir194_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 .north p = true := by
  change ((!walkGuard soko2_2.board support p 194 172 .north || decide (bonus 194 p ≤ bonus 172 p)) && ((PreciseRolling.stayTargets soko2_2.board 172 .north).all (fun landing => !pushGuard support p 194 172 150 landing || decide (bonus 194 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 172 + bonus 172 (change p 172 (some landing)))) && (pushTargets soko2_2.board 172 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 194 172 150 landing || decide (bonus 194 p ≤ 1 - Generated.soko2_2Potential.boulder 172 - Generated.soko2_2Potential.hole landing + bonus 172 (change p 172 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check831 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check832 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir194_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 .south p = true := by
  change ((!walkGuard soko2_2.board support p 194 216 .south || decide (bonus 194 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check833 p, rfl⟩
theorem dir194_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 .east p = true := by
  rfl
theorem dir194_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 .west p = true := by
  change ((!walkGuard soko2_2.board support p 194 193 .west || decide (bonus 194 p ≤ bonus 193 p)) && ((PreciseRolling.stayTargets soko2_2.board 193 .west).all (fun landing => !pushGuard support p 194 193 192 landing || decide (bonus 194 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some landing)))) && (pushTargets soko2_2.board 193 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 194 193 192 landing || decide (bonus 194 p ≤ 1 - Generated.soko2_2Potential.boulder 193 - Generated.soko2_2Potential.hole landing + bonus 193 (change p 193 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check834 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check835 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir194_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 .northEast p = true := by
  rfl
theorem dir194_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 194 171 .northWest || decide (bonus 194 p ≤ bonus 171 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check836 p, rfl⟩
theorem dir194_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 .southEast p = true := by
  rfl
theorem dir194_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 194 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 194 215 .southWest || decide (bonus 194 p ≤ bonus 215 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check837 p, rfl⟩
end NetHack.Sokoban22Refined85
