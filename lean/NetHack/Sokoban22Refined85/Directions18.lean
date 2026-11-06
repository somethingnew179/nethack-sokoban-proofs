import NetHack.Sokoban22Refined85.Directions17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir211_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 .north p = true := by
  change ((!walkGuard soko2_2.board support p 211 189 .north || decide (bonus 211 p ≤ bonus 189 p)) && ((PreciseRolling.stayTargets soko2_2.board 189 .north).all (fun landing => !pushGuard support p 211 189 167 landing || decide (bonus 211 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some landing)))) && (pushTargets soko2_2.board 189 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 211 189 167 landing || decide (bonus 211 p ≤ 1 - Generated.soko2_2Potential.boulder 189 - Generated.soko2_2Potential.hole landing + bonus 189 (change p 189 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check874 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check875 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir211_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 .south p = true := by
  rfl
theorem dir211_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 .east p = true := by
  change ((!walkGuard soko2_2.board support p 211 212 .east || decide (bonus 211 p ≤ bonus 212 p)) && ((PreciseRolling.stayTargets soko2_2.board 212 .east).all (fun landing => !pushGuard support p 211 212 213 landing || decide (bonus 211 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 212 + bonus 212 (change p 212 (some landing)))) && (pushTargets soko2_2.board 212 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 211 212 213 landing || decide (bonus 211 p ≤ 1 - Generated.soko2_2Potential.boulder 212 - Generated.soko2_2Potential.hole landing + bonus 212 (change p 212 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check876 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check877 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir211_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 .west p = true := by
  change ((!walkGuard soko2_2.board support p 211 210 .west || decide (bonus 211 p ≤ bonus 210 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check878 p, rfl⟩
theorem dir211_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 211 190 .northEast || decide (bonus 211 p ≤ bonus 190 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check879 p, rfl⟩
theorem dir211_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 211 188 .northWest || decide (bonus 211 p ≤ bonus 188 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check880 p, rfl⟩
theorem dir211_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 .southEast p = true := by
  rfl
theorem dir211_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 211 .southWest p = true := by
  rfl
theorem dir212_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 .north p = true := by
  change ((!walkGuard soko2_2.board support p 212 190 .north || decide (bonus 212 p ≤ bonus 190 p)) && ((PreciseRolling.stayTargets soko2_2.board 190 .north).all (fun landing => !pushGuard support p 212 190 168 landing || decide (bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 190 + bonus 190 (change p 190 (some landing)))) && (pushTargets soko2_2.board 190 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 212 190 168 landing || decide (bonus 212 p ≤ 1 - Generated.soko2_2Potential.boulder 190 - Generated.soko2_2Potential.hole landing + bonus 190 (change p 190 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check881 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check882 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 .south p = true := by
  rfl
theorem dir212_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 .east p = true := by
  change ((!walkGuard soko2_2.board support p 212 213 .east || decide (bonus 212 p ≤ bonus 213 p)) && ((PreciseRolling.stayTargets soko2_2.board 213 .east).all (fun landing => !pushGuard support p 212 213 214 landing || decide (bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 213 + bonus 213 (change p 213 (some landing)))) && (pushTargets soko2_2.board 213 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 212 213 214 landing || decide (bonus 212 p ≤ 1 - Generated.soko2_2Potential.boulder 213 - Generated.soko2_2Potential.hole landing + bonus 213 (change p 213 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check883 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check884 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 .west p = true := by
  change ((!walkGuard soko2_2.board support p 212 211 .west || decide (bonus 212 p ≤ bonus 211 p)) && ((PreciseRolling.stayTargets soko2_2.board 211 .west).all (fun landing => !pushGuard support p 212 211 210 landing || decide (bonus 212 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 211 + bonus 211 (change p 211 (some landing)))) && (pushTargets soko2_2.board 211 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 212 211 210 landing || decide (bonus 212 p ≤ 1 - Generated.soko2_2Potential.boulder 211 - Generated.soko2_2Potential.hole landing + bonus 211 (change p 211 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check885 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check886 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 212 191 .northEast || decide (bonus 212 p ≤ bonus 191 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check887 p, rfl⟩
theorem dir212_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 212 189 .northWest || decide (bonus 212 p ≤ bonus 189 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check888 p, rfl⟩
theorem dir212_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 .southEast p = true := by
  rfl
theorem dir212_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 212 .southWest p = true := by
  rfl
theorem dir213_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 .north p = true := by
  change ((!walkGuard soko2_2.board support p 213 191 .north || decide (bonus 213 p ≤ bonus 191 p)) && ((PreciseRolling.stayTargets soko2_2.board 191 .north).all (fun landing => !pushGuard support p 213 191 169 landing || decide (bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 191 + bonus 191 (change p 191 (some landing)))) && (pushTargets soko2_2.board 191 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 213 191 169 landing || decide (bonus 213 p ≤ 1 - Generated.soko2_2Potential.boulder 191 - Generated.soko2_2Potential.hole landing + bonus 191 (change p 191 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check889 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check890 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 .south p = true := by
  rfl
theorem dir213_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 .east p = true := by
  change ((!walkGuard soko2_2.board support p 213 214 .east || decide (bonus 213 p ≤ bonus 214 p)) && ((PreciseRolling.stayTargets soko2_2.board 214 .east).all (fun landing => !pushGuard support p 213 214 215 landing || decide (bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 214 + bonus 214 (change p 214 (some landing)))) && (pushTargets soko2_2.board 214 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 213 214 215 landing || decide (bonus 213 p ≤ 1 - Generated.soko2_2Potential.boulder 214 - Generated.soko2_2Potential.hole landing + bonus 214 (change p 214 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check891 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check892 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 .west p = true := by
  change ((!walkGuard soko2_2.board support p 213 212 .west || decide (bonus 213 p ≤ bonus 212 p)) && ((PreciseRolling.stayTargets soko2_2.board 212 .west).all (fun landing => !pushGuard support p 213 212 211 landing || decide (bonus 213 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 212 + bonus 212 (change p 212 (some landing)))) && (pushTargets soko2_2.board 212 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 213 212 211 landing || decide (bonus 213 p ≤ 1 - Generated.soko2_2Potential.boulder 212 - Generated.soko2_2Potential.hole landing + bonus 212 (change p 212 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check893 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check894 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 213 192 .northEast || decide (bonus 213 p ≤ bonus 192 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check895 p, rfl⟩
theorem dir213_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 213 190 .northWest || decide (bonus 213 p ≤ bonus 190 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check896 p, rfl⟩
theorem dir213_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 .southEast p = true := by
  rfl
theorem dir213_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 213 .southWest p = true := by
  rfl
theorem dir214_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 .north p = true := by
  change ((!walkGuard soko2_2.board support p 214 192 .north || decide (bonus 214 p ≤ bonus 192 p)) && ((PreciseRolling.stayTargets soko2_2.board 192 .north).all (fun landing => !pushGuard support p 214 192 170 landing || decide (bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 192 + bonus 192 (change p 192 (some landing)))) && (pushTargets soko2_2.board 192 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 214 192 170 landing || decide (bonus 214 p ≤ 1 - Generated.soko2_2Potential.boulder 192 - Generated.soko2_2Potential.hole landing + bonus 192 (change p 192 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check897 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check898 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir214_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 .south p = true := by
  rfl
theorem dir214_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 .east p = true := by
  change ((!walkGuard soko2_2.board support p 214 215 .east || decide (bonus 214 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko2_2.board 215 .east).all (fun landing => !pushGuard support p 214 215 216 landing || decide (bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko2_2.board 215 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 214 215 216 landing || decide (bonus 214 p ≤ 1 - Generated.soko2_2Potential.boulder 215 - Generated.soko2_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check899 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check900 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir214_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 .west p = true := by
  change ((!walkGuard soko2_2.board support p 214 213 .west || decide (bonus 214 p ≤ bonus 213 p)) && ((PreciseRolling.stayTargets soko2_2.board 213 .west).all (fun landing => !pushGuard support p 214 213 212 landing || decide (bonus 214 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 213 + bonus 213 (change p 213 (some landing)))) && (pushTargets soko2_2.board 213 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 214 213 212 landing || decide (bonus 214 p ≤ 1 - Generated.soko2_2Potential.boulder 213 - Generated.soko2_2Potential.hole landing + bonus 213 (change p 213 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check901 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check902 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir214_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 214 193 .northEast || decide (bonus 214 p ≤ bonus 193 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check903 p, rfl⟩
theorem dir214_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 214 191 .northWest || decide (bonus 214 p ≤ bonus 191 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check904 p, rfl⟩
theorem dir214_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 .southEast p = true := by
  rfl
theorem dir214_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 214 .southWest p = true := by
  rfl
theorem dir215_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 .north p = true := by
  change ((!walkGuard soko2_2.board support p 215 193 .north || decide (bonus 215 p ≤ bonus 193 p)) && ((PreciseRolling.stayTargets soko2_2.board 193 .north).all (fun landing => !pushGuard support p 215 193 171 landing || decide (bonus 215 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 193 + bonus 193 (change p 193 (some landing)))) && (pushTargets soko2_2.board 193 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 215 193 171 landing || decide (bonus 215 p ≤ 1 - Generated.soko2_2Potential.boulder 193 - Generated.soko2_2Potential.hole landing + bonus 193 (change p 193 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check905 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check906 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir215_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 .south p = true := by
  rfl
theorem dir215_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 .east p = true := by
  change ((!walkGuard soko2_2.board support p 215 216 .east || decide (bonus 215 p ≤ bonus 216 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check907 p, rfl⟩
theorem dir215_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 .west p = true := by
  change ((!walkGuard soko2_2.board support p 215 214 .west || decide (bonus 215 p ≤ bonus 214 p)) && ((PreciseRolling.stayTargets soko2_2.board 214 .west).all (fun landing => !pushGuard support p 215 214 213 landing || decide (bonus 215 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 214 + bonus 214 (change p 214 (some landing)))) && (pushTargets soko2_2.board 214 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 215 214 213 landing || decide (bonus 215 p ≤ 1 - Generated.soko2_2Potential.boulder 214 - Generated.soko2_2Potential.hole landing + bonus 214 (change p 214 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check908 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check909 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir215_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 215 194 .northEast || decide (bonus 215 p ≤ bonus 194 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check910 p, rfl⟩
theorem dir215_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 215 192 .northWest || decide (bonus 215 p ≤ bonus 192 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check911 p, rfl⟩
theorem dir215_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 .southEast p = true := by
  rfl
theorem dir215_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 215 .southWest p = true := by
  rfl
theorem dir216_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 .north p = true := by
  change ((!walkGuard soko2_2.board support p 216 194 .north || decide (bonus 216 p ≤ bonus 194 p)) && ((PreciseRolling.stayTargets soko2_2.board 194 .north).all (fun landing => !pushGuard support p 216 194 172 landing || decide (bonus 216 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 194 + bonus 194 (change p 194 (some landing)))) && (pushTargets soko2_2.board 194 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 216 194 172 landing || decide (bonus 216 p ≤ 1 - Generated.soko2_2Potential.boulder 194 - Generated.soko2_2Potential.hole landing + bonus 194 (change p 194 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check912 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check913 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir216_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 .south p = true := by
  rfl
theorem dir216_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 .east p = true := by
  rfl
theorem dir216_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 .west p = true := by
  change ((!walkGuard soko2_2.board support p 216 215 .west || decide (bonus 216 p ≤ bonus 215 p)) && ((PreciseRolling.stayTargets soko2_2.board 215 .west).all (fun landing => !pushGuard support p 216 215 214 landing || decide (bonus 216 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 215 + bonus 215 (change p 215 (some landing)))) && (pushTargets soko2_2.board 215 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 216 215 214 landing || decide (bonus 216 p ≤ 1 - Generated.soko2_2Potential.boulder 215 - Generated.soko2_2Potential.hole landing + bonus 215 (change p 215 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check914 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check915 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir216_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 .northEast p = true := by
  rfl
theorem dir216_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 216 193 .northWest || decide (bonus 216 p ≤ bonus 193 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check916 p, rfl⟩
theorem dir216_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 .southEast p = true := by
  rfl
theorem dir216_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 216 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
