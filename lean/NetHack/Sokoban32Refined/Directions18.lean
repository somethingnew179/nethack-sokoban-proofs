import NetHack.Sokoban32Refined.Directions17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir206_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 .north p = true := by
  change ((!walkGuard soko3_2.board support p 206 180 .north || decide (bonus 206 p ≤ bonus 180 p)) && ((PreciseRolling.stayTargets soko3_2.board 180 .north).all (fun landing => !pushGuard support p 206 180 154 landing || decide (bonus 206 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 180 + bonus 180 (change p 180 (some landing)))) && (pushTargets soko3_2.board 180 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 206 180 154 landing || decide (bonus 206 p ≤ 1 - Generated.soko3_2Potential.boulder 180 - Generated.soko3_2Potential.hole landing + bonus 180 (change p 180 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check937 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check938 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir206_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 .south p = true := by
  change ((!walkGuard soko3_2.board support p 206 232 .south || decide (bonus 206 p ≤ bonus 232 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check939 p, rfl⟩
theorem dir206_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 .east p = true := by
  rfl
theorem dir206_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 .west p = true := by
  change ((!walkGuard soko3_2.board support p 206 205 .west || decide (bonus 206 p ≤ bonus 205 p)) && ((PreciseRolling.stayTargets soko3_2.board 205 .west).all (fun landing => !pushGuard support p 206 205 204 landing || decide (bonus 206 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some landing)))) && (pushTargets soko3_2.board 205 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 206 205 204 landing || decide (bonus 206 p ≤ 1 - Generated.soko3_2Potential.boulder 205 - Generated.soko3_2Potential.hole landing + bonus 205 (change p 205 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check940 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check941 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir206_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 .northEast p = true := by
  rfl
theorem dir206_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 206 179 .northWest || decide (bonus 206 p ≤ bonus 179 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check942 p, rfl⟩
theorem dir206_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 .southEast p = true := by
  rfl
theorem dir206_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 206 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 206 231 .southWest || decide (bonus 206 p ≤ bonus 231 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check943 p, rfl⟩
theorem dir209_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 .north p = true := by
  change ((!walkGuard soko3_2.board support p 209 183 .north || decide (bonus 209 p ≤ bonus 183 p)) && ((PreciseRolling.stayTargets soko3_2.board 183 .north).all (fun landing => !pushGuard support p 209 183 157 landing || decide (bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 183 + bonus 183 (change p 183 (some landing)))) && (pushTargets soko3_2.board 183 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 209 183 157 landing || decide (bonus 209 p ≤ 1 - Generated.soko3_2Potential.boulder 183 - Generated.soko3_2Potential.hole landing + bonus 183 (change p 183 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check944 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check945 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir209_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 .south p = true := by
  change ((!walkGuard soko3_2.board support p 209 235 .south || decide (bonus 209 p ≤ bonus 235 p)) && ((PreciseRolling.stayTargets soko3_2.board 235 .south).all (fun landing => !pushGuard support p 209 235 261 landing || decide (bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 235 + bonus 235 (change p 235 (some landing)))) && (pushTargets soko3_2.board 235 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 209 235 261 landing || decide (bonus 209 p ≤ 1 - Generated.soko3_2Potential.boulder 235 - Generated.soko3_2Potential.hole landing + bonus 235 (change p 235 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check946 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check947 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir209_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 .east p = true := by
  change ((!walkGuard soko3_2.board support p 209 210 .east || decide (bonus 209 p ≤ bonus 210 p)) && ((PreciseRolling.stayTargets soko3_2.board 210 .east).all (fun landing => !pushGuard support p 209 210 211 landing || decide (bonus 209 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 210 + bonus 210 (change p 210 (some landing)))) && (pushTargets soko3_2.board 210 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 209 210 211 landing || decide (bonus 209 p ≤ 1 - Generated.soko3_2Potential.boulder 210 - Generated.soko3_2Potential.hole landing + bonus 210 (change p 210 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check948 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check949 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir209_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 .west p = true := by
  rfl
theorem dir209_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 .northEast p = true := by
  rfl
theorem dir209_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 .northWest p = true := by
  rfl
theorem dir209_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 .southEast p = true := by
  rfl
theorem dir209_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 209 .southWest p = true := by
  rfl
theorem dir210_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 .north p = true := by
  rfl
theorem dir210_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 .south p = true := by
  rfl
theorem dir210_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 .east p = true := by
  change ((!walkGuard soko3_2.board support p 210 211 .east || decide (bonus 210 p ≤ bonus 211 p)) && ((PreciseRolling.stayTargets soko3_2.board 211 .east).all (fun landing => !pushGuard support p 210 211 212 landing || decide (bonus 210 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 211 + bonus 211 (change p 211 (some landing)))) && (pushTargets soko3_2.board 211 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 210 211 212 landing || decide (bonus 210 p ≤ 1 - Generated.soko3_2Potential.boulder 211 - Generated.soko3_2Potential.hole landing + bonus 211 (change p 211 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check950 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check951 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir210_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 .west p = true := by
  change ((!walkGuard soko3_2.board support p 210 209 .west || decide (bonus 210 p ≤ bonus 209 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check952 p, rfl⟩
theorem dir210_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 .northEast p = true := by
  rfl
theorem dir210_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 210 183 .northWest || decide (bonus 210 p ≤ bonus 183 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check953 p, rfl⟩
theorem dir210_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 .southEast p = true := by
  rfl
theorem dir210_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 210 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 210 235 .southWest || decide (bonus 210 p ≤ bonus 235 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check954 p, rfl⟩
theorem dir211_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 .north p = true := by
  rfl
theorem dir211_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 .south p = true := by
  rfl
theorem dir211_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 .east p = true := by
  change ((!walkGuard soko3_2.board support p 211 212 .east || decide (bonus 211 p ≤ bonus 212 p)) && ((PreciseRolling.stayTargets soko3_2.board 212 .east).all (fun landing => !pushGuard support p 211 212 213 landing || decide (bonus 211 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 212 + bonus 212 (change p 212 (some landing)))) && (pushTargets soko3_2.board 212 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 211 212 213 landing || decide (bonus 211 p ≤ 1 - Generated.soko3_2Potential.boulder 212 - Generated.soko3_2Potential.hole landing + bonus 212 (change p 212 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check955 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check956 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir211_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 .west p = true := by
  change ((!walkGuard soko3_2.board support p 211 210 .west || decide (bonus 211 p ≤ bonus 210 p)) && ((PreciseRolling.stayTargets soko3_2.board 210 .west).all (fun landing => !pushGuard support p 211 210 209 landing || decide (bonus 211 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 210 + bonus 210 (change p 210 (some landing)))) && (pushTargets soko3_2.board 210 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 211 210 209 landing || decide (bonus 211 p ≤ 1 - Generated.soko3_2Potential.boulder 210 - Generated.soko3_2Potential.hole landing + bonus 210 (change p 210 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check957 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check958 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir211_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 .northEast p = true := by
  rfl
theorem dir211_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 .northWest p = true := by
  rfl
theorem dir211_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 .southEast p = true := by
  rfl
theorem dir211_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 211 .southWest p = true := by
  rfl
theorem dir212_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 .north p = true := by
  rfl
theorem dir212_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 .south p = true := by
  rfl
theorem dir212_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 .east p = true := by
  change ((!walkGuard soko3_2.board support p 212 213 .east || decide (bonus 212 p ≤ bonus 213 p)) && ((PreciseRolling.stayTargets soko3_2.board 213 .east).all (fun landing => !pushGuard support p 212 213 214 landing || decide (bonus 212 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 213 + bonus 213 (change p 213 (some landing)))) && (pushTargets soko3_2.board 213 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 212 213 214 landing || decide (bonus 212 p ≤ 1 - Generated.soko3_2Potential.boulder 213 - Generated.soko3_2Potential.hole landing + bonus 213 (change p 213 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check959 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check960 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 .west p = true := by
  change ((!walkGuard soko3_2.board support p 212 211 .west || decide (bonus 212 p ≤ bonus 211 p)) && ((PreciseRolling.stayTargets soko3_2.board 211 .west).all (fun landing => !pushGuard support p 212 211 210 landing || decide (bonus 212 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 211 + bonus 211 (change p 211 (some landing)))) && (pushTargets soko3_2.board 211 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 212 211 210 landing || decide (bonus 212 p ≤ 1 - Generated.soko3_2Potential.boulder 211 - Generated.soko3_2Potential.hole landing + bonus 211 (change p 211 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check961 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check962 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir212_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 .northEast p = true := by
  rfl
theorem dir212_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 .northWest p = true := by
  rfl
theorem dir212_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 212 239 .southEast || decide (bonus 212 p ≤ bonus 239 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check963 p, rfl⟩
theorem dir212_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 212 .southWest p = true := by
  rfl
theorem dir213_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 .north p = true := by
  rfl
theorem dir213_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 .south p = true := by
  change ((!walkGuard soko3_2.board support p 213 239 .south || decide (bonus 213 p ≤ bonus 239 p)) && ((PreciseRolling.stayTargets soko3_2.board 239 .south).all (fun landing => !pushGuard support p 213 239 265 landing || decide (bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 239 + bonus 239 (change p 239 (some landing)))) && (pushTargets soko3_2.board 239 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 213 239 265 landing || decide (bonus 213 p ≤ 1 - Generated.soko3_2Potential.boulder 239 - Generated.soko3_2Potential.hole landing + bonus 239 (change p 239 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check964 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check965 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 .east p = true := by
  change ((!walkGuard soko3_2.board support p 213 214 .east || decide (bonus 213 p ≤ bonus 214 p)) && ((PreciseRolling.stayTargets soko3_2.board 214 .east).all (fun landing => !pushGuard support p 213 214 215 landing || decide (bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 214 + bonus 214 (change p 214 (some landing)))) && (pushTargets soko3_2.board 214 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 213 214 215 landing || decide (bonus 213 p ≤ 1 - Generated.soko3_2Potential.boulder 214 - Generated.soko3_2Potential.hole landing + bonus 214 (change p 214 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check966 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check967 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 .west p = true := by
  change ((!walkGuard soko3_2.board support p 213 212 .west || decide (bonus 213 p ≤ bonus 212 p)) && ((PreciseRolling.stayTargets soko3_2.board 212 .west).all (fun landing => !pushGuard support p 213 212 211 landing || decide (bonus 213 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 212 + bonus 212 (change p 212 (some landing)))) && (pushTargets soko3_2.board 212 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 213 212 211 landing || decide (bonus 213 p ≤ 1 - Generated.soko3_2Potential.boulder 212 - Generated.soko3_2Potential.hole landing + bonus 212 (change p 212 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check968 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check969 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir213_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 213 188 .northEast || decide (bonus 213 p ≤ bonus 188 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check970 p, rfl⟩
theorem dir213_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 .northWest p = true := by
  rfl
theorem dir213_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 .southEast p = true := by
  rfl
theorem dir213_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 213 .southWest p = true := by
  rfl
end NetHack.Sokoban32Refined
