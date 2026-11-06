import NetHack.Sokoban32Refined.Directions16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir200_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 .north p = true := by
  change ((!walkGuard soko3_2.board support p 200 174 .north || decide (bonus 200 p ≤ bonus 174 p)) && ((PreciseRolling.stayTargets soko3_2.board 174 .north).all (fun landing => !pushGuard support p 200 174 148 landing || decide (bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some landing)))) && (pushTargets soko3_2.board 174 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 200 174 148 landing || decide (bonus 200 p ≤ 1 - Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.hole landing + bonus 174 (change p 174 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check872 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check873 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir200_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 .south p = true := by
  change ((!walkGuard soko3_2.board support p 200 226 .south || decide (bonus 200 p ≤ bonus 226 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check874 p, rfl⟩
theorem dir200_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 .east p = true := by
  change ((!walkGuard soko3_2.board support p 200 201 .east || decide (bonus 200 p ≤ bonus 201 p)) && ((PreciseRolling.stayTargets soko3_2.board 201 .east).all (fun landing => !pushGuard support p 200 201 202 landing || decide (bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some landing)))) && (pushTargets soko3_2.board 201 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 200 201 202 landing || decide (bonus 200 p ≤ 1 - Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.hole landing + bonus 201 (change p 201 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check875 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check876 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir200_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 .west p = true := by
  change ((!walkGuard soko3_2.board support p 200 199 .west || decide (bonus 200 p ≤ bonus 199 p)) && ((PreciseRolling.stayTargets soko3_2.board 199 .west).all (fun landing => !pushGuard support p 200 199 198 landing || decide (bonus 200 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 199 + bonus 199 (change p 199 (some landing)))) && (pushTargets soko3_2.board 199 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 200 199 198 landing || decide (bonus 200 p ≤ 1 - Generated.soko3_2Potential.boulder 199 - Generated.soko3_2Potential.hole landing + bonus 199 (change p 199 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check877 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check878 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir200_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 200 175 .northEast || decide (bonus 200 p ≤ bonus 175 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check879 p, rfl⟩
theorem dir200_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 200 173 .northWest || decide (bonus 200 p ≤ bonus 173 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check880 p, rfl⟩
theorem dir200_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 200 227 .southEast || decide (bonus 200 p ≤ bonus 227 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check881 p, rfl⟩
theorem dir200_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 200 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 200 225 .southWest || decide (bonus 200 p ≤ bonus 225 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check882 p, rfl⟩
theorem dir201_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 .north p = true := by
  change ((!walkGuard soko3_2.board support p 201 175 .north || decide (bonus 201 p ≤ bonus 175 p)) && ((PreciseRolling.stayTargets soko3_2.board 175 .north).all (fun landing => !pushGuard support p 201 175 149 landing || decide (bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some landing)))) && (pushTargets soko3_2.board 175 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 201 175 149 landing || decide (bonus 201 p ≤ 1 - Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.hole landing + bonus 175 (change p 175 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check883 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check884 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir201_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 .south p = true := by
  change ((!walkGuard soko3_2.board support p 201 227 .south || decide (bonus 201 p ≤ bonus 227 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check885 p, rfl⟩
theorem dir201_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 .east p = true := by
  change ((!walkGuard soko3_2.board support p 201 202 .east || decide (bonus 201 p ≤ bonus 202 p)) && ((PreciseRolling.stayTargets soko3_2.board 202 .east).all (fun landing => !pushGuard support p 201 202 203 landing || decide (bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some landing)))) && (pushTargets soko3_2.board 202 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 201 202 203 landing || decide (bonus 201 p ≤ 1 - Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.hole landing + bonus 202 (change p 202 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check886 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check887 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir201_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 .west p = true := by
  change ((!walkGuard soko3_2.board support p 201 200 .west || decide (bonus 201 p ≤ bonus 200 p)) && ((PreciseRolling.stayTargets soko3_2.board 200 .west).all (fun landing => !pushGuard support p 201 200 199 landing || decide (bonus 201 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 200 + bonus 200 (change p 200 (some landing)))) && (pushTargets soko3_2.board 200 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 201 200 199 landing || decide (bonus 201 p ≤ 1 - Generated.soko3_2Potential.boulder 200 - Generated.soko3_2Potential.hole landing + bonus 200 (change p 200 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check888 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check889 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir201_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 201 176 .northEast || decide (bonus 201 p ≤ bonus 176 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check890 p, rfl⟩
theorem dir201_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 201 174 .northWest || decide (bonus 201 p ≤ bonus 174 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check891 p, rfl⟩
theorem dir201_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 201 228 .southEast || decide (bonus 201 p ≤ bonus 228 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check892 p, rfl⟩
theorem dir201_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 201 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 201 226 .southWest || decide (bonus 201 p ≤ bonus 226 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check893 p, rfl⟩
theorem dir202_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 .north p = true := by
  change ((!walkGuard soko3_2.board support p 202 176 .north || decide (bonus 202 p ≤ bonus 176 p)) && ((PreciseRolling.stayTargets soko3_2.board 176 .north).all (fun landing => !pushGuard support p 202 176 150 landing || decide (bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some landing)))) && (pushTargets soko3_2.board 176 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 202 176 150 landing || decide (bonus 202 p ≤ 1 - Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.hole landing + bonus 176 (change p 176 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check894 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check895 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir202_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 .south p = true := by
  change ((!walkGuard soko3_2.board support p 202 228 .south || decide (bonus 202 p ≤ bonus 228 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check896 p, rfl⟩
theorem dir202_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 .east p = true := by
  change ((!walkGuard soko3_2.board support p 202 203 .east || decide (bonus 202 p ≤ bonus 203 p)) && ((PreciseRolling.stayTargets soko3_2.board 203 .east).all (fun landing => !pushGuard support p 202 203 204 landing || decide (bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some landing)))) && (pushTargets soko3_2.board 203 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 202 203 204 landing || decide (bonus 202 p ≤ 1 - Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.hole landing + bonus 203 (change p 203 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check897 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check898 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir202_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 .west p = true := by
  change ((!walkGuard soko3_2.board support p 202 201 .west || decide (bonus 202 p ≤ bonus 201 p)) && ((PreciseRolling.stayTargets soko3_2.board 201 .west).all (fun landing => !pushGuard support p 202 201 200 landing || decide (bonus 202 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some landing)))) && (pushTargets soko3_2.board 201 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 202 201 200 landing || decide (bonus 202 p ≤ 1 - Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.hole landing + bonus 201 (change p 201 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check899 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check900 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir202_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 202 177 .northEast || decide (bonus 202 p ≤ bonus 177 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check901 p, rfl⟩
theorem dir202_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 202 175 .northWest || decide (bonus 202 p ≤ bonus 175 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check902 p, rfl⟩
theorem dir202_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 202 229 .southEast || decide (bonus 202 p ≤ bonus 229 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check903 p, rfl⟩
theorem dir202_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 202 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 202 227 .southWest || decide (bonus 202 p ≤ bonus 227 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check904 p, rfl⟩
theorem dir203_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 .north p = true := by
  change ((!walkGuard soko3_2.board support p 203 177 .north || decide (bonus 203 p ≤ bonus 177 p)) && ((PreciseRolling.stayTargets soko3_2.board 177 .north).all (fun landing => !pushGuard support p 203 177 151 landing || decide (bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some landing)))) && (pushTargets soko3_2.board 177 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 203 177 151 landing || decide (bonus 203 p ≤ 1 - Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.hole landing + bonus 177 (change p 177 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check905 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check906 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir203_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 .south p = true := by
  change ((!walkGuard soko3_2.board support p 203 229 .south || decide (bonus 203 p ≤ bonus 229 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check907 p, rfl⟩
theorem dir203_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 .east p = true := by
  change ((!walkGuard soko3_2.board support p 203 204 .east || decide (bonus 203 p ≤ bonus 204 p)) && ((PreciseRolling.stayTargets soko3_2.board 204 .east).all (fun landing => !pushGuard support p 203 204 205 landing || decide (bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some landing)))) && (pushTargets soko3_2.board 204 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 203 204 205 landing || decide (bonus 203 p ≤ 1 - Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.hole landing + bonus 204 (change p 204 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check908 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check909 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir203_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 .west p = true := by
  change ((!walkGuard soko3_2.board support p 203 202 .west || decide (bonus 203 p ≤ bonus 202 p)) && ((PreciseRolling.stayTargets soko3_2.board 202 .west).all (fun landing => !pushGuard support p 203 202 201 landing || decide (bonus 203 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some landing)))) && (pushTargets soko3_2.board 202 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 203 202 201 landing || decide (bonus 203 p ≤ 1 - Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.hole landing + bonus 202 (change p 202 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check910 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check911 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir203_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 203 178 .northEast || decide (bonus 203 p ≤ bonus 178 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check912 p, rfl⟩
theorem dir203_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 203 176 .northWest || decide (bonus 203 p ≤ bonus 176 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check913 p, rfl⟩
theorem dir203_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 203 230 .southEast || decide (bonus 203 p ≤ bonus 230 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check914 p, rfl⟩
theorem dir203_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 203 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 203 228 .southWest || decide (bonus 203 p ≤ bonus 228 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check915 p, rfl⟩
theorem dir204_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 .north p = true := by
  change ((!walkGuard soko3_2.board support p 204 178 .north || decide (bonus 204 p ≤ bonus 178 p)) && ((PreciseRolling.stayTargets soko3_2.board 178 .north).all (fun landing => !pushGuard support p 204 178 152 landing || decide (bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some landing)))) && (pushTargets soko3_2.board 178 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 204 178 152 landing || decide (bonus 204 p ≤ 1 - Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.hole landing + bonus 178 (change p 178 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check916 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check917 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir204_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 .south p = true := by
  change ((!walkGuard soko3_2.board support p 204 230 .south || decide (bonus 204 p ≤ bonus 230 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check918 p, rfl⟩
theorem dir204_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 .east p = true := by
  change ((!walkGuard soko3_2.board support p 204 205 .east || decide (bonus 204 p ≤ bonus 205 p)) && ((PreciseRolling.stayTargets soko3_2.board 205 .east).all (fun landing => !pushGuard support p 204 205 206 landing || decide (bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some landing)))) && (pushTargets soko3_2.board 205 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 204 205 206 landing || decide (bonus 204 p ≤ 1 - Generated.soko3_2Potential.boulder 205 - Generated.soko3_2Potential.hole landing + bonus 205 (change p 205 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check919 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check920 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir204_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 .west p = true := by
  change ((!walkGuard soko3_2.board support p 204 203 .west || decide (bonus 204 p ≤ bonus 203 p)) && ((PreciseRolling.stayTargets soko3_2.board 203 .west).all (fun landing => !pushGuard support p 204 203 202 landing || decide (bonus 204 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some landing)))) && (pushTargets soko3_2.board 203 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 204 203 202 landing || decide (bonus 204 p ≤ 1 - Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.hole landing + bonus 203 (change p 203 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check921 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check922 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir204_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 204 179 .northEast || decide (bonus 204 p ≤ bonus 179 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check923 p, rfl⟩
theorem dir204_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 204 177 .northWest || decide (bonus 204 p ≤ bonus 177 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check924 p, rfl⟩
theorem dir204_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 204 231 .southEast || decide (bonus 204 p ≤ bonus 231 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check925 p, rfl⟩
theorem dir204_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 204 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 204 229 .southWest || decide (bonus 204 p ≤ bonus 229 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check926 p, rfl⟩
theorem dir205_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 .north p = true := by
  change ((!walkGuard soko3_2.board support p 205 179 .north || decide (bonus 205 p ≤ bonus 179 p)) && ((PreciseRolling.stayTargets soko3_2.board 179 .north).all (fun landing => !pushGuard support p 205 179 153 landing || decide (bonus 205 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some landing)))) && (pushTargets soko3_2.board 179 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 205 179 153 landing || decide (bonus 205 p ≤ 1 - Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.hole landing + bonus 179 (change p 179 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check927 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check928 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir205_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 .south p = true := by
  change ((!walkGuard soko3_2.board support p 205 231 .south || decide (bonus 205 p ≤ bonus 231 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check929 p, rfl⟩
theorem dir205_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 .east p = true := by
  change ((!walkGuard soko3_2.board support p 205 206 .east || decide (bonus 205 p ≤ bonus 206 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check930 p, rfl⟩
theorem dir205_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 .west p = true := by
  change ((!walkGuard soko3_2.board support p 205 204 .west || decide (bonus 205 p ≤ bonus 204 p)) && ((PreciseRolling.stayTargets soko3_2.board 204 .west).all (fun landing => !pushGuard support p 205 204 203 landing || decide (bonus 205 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some landing)))) && (pushTargets soko3_2.board 204 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 205 204 203 landing || decide (bonus 205 p ≤ 1 - Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.hole landing + bonus 204 (change p 204 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check931 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check932 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir205_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 205 180 .northEast || decide (bonus 205 p ≤ bonus 180 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check933 p, rfl⟩
theorem dir205_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 205 178 .northWest || decide (bonus 205 p ≤ bonus 178 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check934 p, rfl⟩
theorem dir205_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 205 232 .southEast || decide (bonus 205 p ≤ bonus 232 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check935 p, rfl⟩
theorem dir205_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 205 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 205 230 .southWest || decide (bonus 205 p ≤ bonus 230 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check936 p, rfl⟩
end NetHack.Sokoban32Refined
