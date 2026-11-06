import NetHack.Sokoban32Refined.Directions15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir183_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 .north p = true := by
  change ((!walkGuard soko3_2.board support p 183 157 .north || decide (bonus 183 p ≤ bonus 157 p)) && ((PreciseRolling.stayTargets soko3_2.board 157 .north).all (fun landing => !pushGuard support p 183 157 131 landing || decide (bonus 183 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 157 + bonus 157 (change p 157 (some landing)))) && (pushTargets soko3_2.board 157 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 183 157 131 landing || decide (bonus 183 p ≤ 1 - Generated.soko3_2Potential.boulder 157 - Generated.soko3_2Potential.hole landing + bonus 157 (change p 157 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check829 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check830 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir183_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 .south p = true := by
  change ((!walkGuard soko3_2.board support p 183 209 .south || decide (bonus 183 p ≤ bonus 209 p)) && ((PreciseRolling.stayTargets soko3_2.board 209 .south).all (fun landing => !pushGuard support p 183 209 235 landing || decide (bonus 183 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 209 + bonus 209 (change p 209 (some landing)))) && (pushTargets soko3_2.board 209 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 183 209 235 landing || decide (bonus 183 p ≤ 1 - Generated.soko3_2Potential.boulder 209 - Generated.soko3_2Potential.hole landing + bonus 209 (change p 209 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check831 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check832 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir183_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 .east p = true := by
  rfl
theorem dir183_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 .west p = true := by
  rfl
theorem dir183_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 183 158 .northEast || decide (bonus 183 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check833 p, rfl⟩
theorem dir183_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 .northWest p = true := by
  rfl
theorem dir183_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 183 210 .southEast || decide (bonus 183 p ≤ bonus 210 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check834 p, rfl⟩
theorem dir183_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 183 .southWest p = true := by
  rfl
theorem dir188_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 .north p = true := by
  change ((!walkGuard soko3_2.board support p 188 162 .north || decide (bonus 188 p ≤ bonus 162 p)) && ((PreciseRolling.stayTargets soko3_2.board 162 .north).all (fun landing => !pushGuard support p 188 162 136 landing || decide (bonus 188 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 162 + bonus 162 (change p 162 (some landing)))) && (pushTargets soko3_2.board 162 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 188 162 136 landing || decide (bonus 188 p ≤ 1 - Generated.soko3_2Potential.boulder 162 - Generated.soko3_2Potential.hole landing + bonus 162 (change p 162 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check835 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check836 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir188_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 .south p = true := by
  change ((!walkGuard soko3_2.board support p 188 214 .south || decide (bonus 188 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check837 p, rfl⟩
theorem dir188_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 .east p = true := by
  change ((!walkGuard soko3_2.board support p 188 189 .east || decide (bonus 188 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check838 p, rfl⟩
theorem dir188_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 .west p = true := by
  rfl
theorem dir188_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 188 163 .northEast || decide (bonus 188 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check839 p, rfl⟩
theorem dir188_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 188 161 .northWest || decide (bonus 188 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check840 p, rfl⟩
theorem dir188_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 188 215 .southEast || decide (bonus 188 p ≤ bonus 215 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check841 p, rfl⟩
theorem dir188_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 188 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 188 213 .southWest || decide (bonus 188 p ≤ bonus 213 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check842 p, rfl⟩
theorem dir189_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 .north p = true := by
  change ((!walkGuard soko3_2.board support p 189 163 .north || decide (bonus 189 p ≤ bonus 163 p)) && ((PreciseRolling.stayTargets soko3_2.board 163 .north).all (fun landing => !pushGuard support p 189 163 137 landing || decide (bonus 189 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 163 + bonus 163 (change p 163 (some landing)))) && (pushTargets soko3_2.board 163 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 189 163 137 landing || decide (bonus 189 p ≤ 1 - Generated.soko3_2Potential.boulder 163 - Generated.soko3_2Potential.hole landing + bonus 163 (change p 163 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check843 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check844 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir189_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 .south p = true := by
  change ((!walkGuard soko3_2.board support p 189 215 .south || decide (bonus 189 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko3_2.board 215 .south).all (fun landing => !pushGuard support p 189 215 241 landing || decide (bonus 189 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko3_2.board 215 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 189 215 241 landing || decide (bonus 189 p ≤ 1 - Generated.soko3_2Potential.boulder 215 - Generated.soko3_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check845 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check846 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir189_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 .east p = true := by
  rfl
theorem dir189_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 .west p = true := by
  change ((!walkGuard soko3_2.board support p 189 188 .west || decide (bonus 189 p ≤ bonus 188 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check847 p, rfl⟩
theorem dir189_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 .northEast p = true := by
  rfl
theorem dir189_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 189 162 .northWest || decide (bonus 189 p ≤ bonus 162 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check848 p, rfl⟩
theorem dir189_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 189 216 .southEast || decide (bonus 189 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check849 p, rfl⟩
theorem dir189_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 189 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 189 214 .southWest || decide (bonus 189 p ≤ bonus 214 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check850 p, rfl⟩
theorem dir192_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 .north p = true := by
  change ((!walkGuard soko3_2.board support p 192 166 .north || decide (bonus 192 p ≤ bonus 166 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check851 p, rfl⟩
theorem dir192_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 .south p = true := by
  change ((!walkGuard soko3_2.board support p 192 218 .south || decide (bonus 192 p ≤ bonus 218 p)) && ((PreciseRolling.stayTargets soko3_2.board 218 .south).all (fun landing => !pushGuard support p 192 218 244 landing || decide (bonus 192 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 218 + bonus 218 (change p 218 (some landing)))) && (pushTargets soko3_2.board 218 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 192 218 244 landing || decide (bonus 192 p ≤ 1 - Generated.soko3_2Potential.boulder 218 - Generated.soko3_2Potential.hole landing + bonus 218 (change p 218 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check852 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check853 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir192_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 .east p = true := by
  rfl
theorem dir192_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 .west p = true := by
  rfl
theorem dir192_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 .northEast p = true := by
  rfl
theorem dir192_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 192 165 .northWest || decide (bonus 192 p ≤ bonus 165 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check854 p, rfl⟩
theorem dir192_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 .southEast p = true := by
  rfl
theorem dir192_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 192 .southWest p = true := by
  rfl
theorem dir198_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 .north p = true := by
  change ((!walkGuard soko3_2.board support p 198 172 .north || decide (bonus 198 p ≤ bonus 172 p)) && ((PreciseRolling.stayTargets soko3_2.board 172 .north).all (fun landing => !pushGuard support p 198 172 146 landing || decide (bonus 198 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 172 + bonus 172 (change p 172 (some landing)))) && (pushTargets soko3_2.board 172 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 198 172 146 landing || decide (bonus 198 p ≤ 1 - Generated.soko3_2Potential.boulder 172 - Generated.soko3_2Potential.hole landing + bonus 172 (change p 172 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check855 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check856 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir198_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 .south p = true := by
  change ((!walkGuard soko3_2.board support p 198 224 .south || decide (bonus 198 p ≤ bonus 224 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check857 p, rfl⟩
theorem dir198_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 .east p = true := by
  change ((!walkGuard soko3_2.board support p 198 199 .east || decide (bonus 198 p ≤ bonus 199 p)) && ((PreciseRolling.stayTargets soko3_2.board 199 .east).all (fun landing => !pushGuard support p 198 199 200 landing || decide (bonus 198 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some landing)))) && (pushTargets soko3_2.board 199 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 198 199 200 landing || decide (bonus 198 p ≤ 1 - Generated.soko3_2Potential.boulder 199 - Generated.soko3_2Potential.hole landing + bonus 199 (change p 199 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check858 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check859 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir198_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 .west p = true := by
  rfl
theorem dir198_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 198 173 .northEast || decide (bonus 198 p ≤ bonus 173 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check860 p, rfl⟩
theorem dir198_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 .northWest p = true := by
  rfl
theorem dir198_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 198 225 .southEast || decide (bonus 198 p ≤ bonus 225 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check861 p, rfl⟩
theorem dir198_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 198 .southWest p = true := by
  rfl
theorem dir199_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 .north p = true := by
  change ((!walkGuard soko3_2.board support p 199 173 .north || decide (bonus 199 p ≤ bonus 173 p)) && ((PreciseRolling.stayTargets soko3_2.board 173 .north).all (fun landing => !pushGuard support p 199 173 147 landing || decide (bonus 199 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 173 + bonus 173 (change p 173 (some landing)))) && (pushTargets soko3_2.board 173 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 199 173 147 landing || decide (bonus 199 p ≤ 1 - Generated.soko3_2Potential.boulder 173 - Generated.soko3_2Potential.hole landing + bonus 173 (change p 173 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check862 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check863 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir199_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 .south p = true := by
  change ((!walkGuard soko3_2.board support p 199 225 .south || decide (bonus 199 p ≤ bonus 225 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check864 p, rfl⟩
theorem dir199_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 .east p = true := by
  change ((!walkGuard soko3_2.board support p 199 200 .east || decide (bonus 199 p ≤ bonus 200 p)) && ((PreciseRolling.stayTargets soko3_2.board 200 .east).all (fun landing => !pushGuard support p 199 200 201 landing || decide (bonus 199 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some landing)))) && (pushTargets soko3_2.board 200 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 199 200 201 landing || decide (bonus 199 p ≤ 1 - Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.hole landing + bonus 200 (change p 200 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check865 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check866 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir199_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 .west p = true := by
  change ((!walkGuard soko3_2.board support p 199 198 .west || decide (bonus 199 p ≤ bonus 198 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check867 p, rfl⟩
theorem dir199_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 199 174 .northEast || decide (bonus 199 p ≤ bonus 174 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check868 p, rfl⟩
theorem dir199_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 199 172 .northWest || decide (bonus 199 p ≤ bonus 172 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check869 p, rfl⟩
theorem dir199_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 199 226 .southEast || decide (bonus 199 p ≤ bonus 226 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check870 p, rfl⟩
theorem dir199_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 199 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 199 224 .southWest || decide (bonus 199 p ≤ bonus 224 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check871 p, rfl⟩
end NetHack.Sokoban32Refined
