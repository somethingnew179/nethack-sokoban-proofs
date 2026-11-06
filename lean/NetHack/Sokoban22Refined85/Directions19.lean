import NetHack.Sokoban22Refined85.Directions18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir218_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 .north p = true := by
  rfl
theorem dir218_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 .south p = true := by
  change ((!walkGuard soko2_2.board support p 218 240 .south || decide (bonus 218 p ≤ bonus 240 p)) && ((PreciseRolling.stayTargets soko2_2.board 240 .south).all (fun landing => !pushGuard support p 218 240 262 landing || decide (bonus 218 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 240 + bonus 240 (change p 240 (some landing)))) && (pushTargets soko2_2.board 240 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 218 240 262 landing || decide (bonus 218 p ≤ 1 - Generated.soko2_2Potential.boulder 240 - Generated.soko2_2Potential.hole landing + bonus 240 (change p 240 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check917 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check918 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir218_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 .east p = true := by
  rfl
theorem dir218_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 .west p = true := by
  rfl
theorem dir218_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 .northEast p = true := by
  rfl
theorem dir218_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 .northWest p = true := by
  rfl
theorem dir218_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 .southEast p = true := by
  rfl
theorem dir218_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 218 .southWest p = true := by
  rfl
theorem dir223_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 .north p = true := by
  change ((!walkGuard soko2_2.board support p 223 201 .north || decide (bonus 223 p ≤ bonus 201 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check919 p, rfl⟩
theorem dir223_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 .south p = true := by
  change ((!walkGuard soko2_2.board support p 223 245 .south || decide (bonus 223 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check920 p, rfl⟩
theorem dir223_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 .east p = true := by
  change ((!walkGuard soko2_2.board support p 223 224 .east || decide (bonus 223 p ≤ bonus 224 p)) && ((PreciseRolling.stayTargets soko2_2.board 224 .east).all (fun landing => !pushGuard support p 223 224 225 landing || decide (bonus 223 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some landing)))) && (pushTargets soko2_2.board 224 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 223 224 225 landing || decide (bonus 223 p ≤ 1 - Generated.soko2_2Potential.boulder 224 - Generated.soko2_2Potential.hole landing + bonus 224 (change p 224 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check921 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check922 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir223_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 .west p = true := by
  rfl
theorem dir223_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 223 202 .northEast || decide (bonus 223 p ≤ bonus 202 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check923 p, rfl⟩
theorem dir223_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 223 200 .northWest || decide (bonus 223 p ≤ bonus 200 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check924 p, rfl⟩
theorem dir223_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 223 246 .southEast || decide (bonus 223 p ≤ bonus 246 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check925 p, rfl⟩
theorem dir223_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 223 .southWest p = true := by
  rfl
theorem dir224_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 .north p = true := by
  change ((!walkGuard soko2_2.board support p 224 202 .north || decide (bonus 224 p ≤ bonus 202 p)) && ((PreciseRolling.stayTargets soko2_2.board 202 .north).all (fun landing => !pushGuard support p 224 202 180 landing || decide (bonus 224 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 202 + bonus 202 (change p 202 (some landing)))) && (pushTargets soko2_2.board 202 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 224 202 180 landing || decide (bonus 224 p ≤ 1 - Generated.soko2_2Potential.boulder 202 - Generated.soko2_2Potential.hole landing + bonus 202 (change p 202 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check926 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check927 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir224_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 .south p = true := by
  change ((!walkGuard soko2_2.board support p 224 246 .south || decide (bonus 224 p ≤ bonus 246 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check928 p, rfl⟩
theorem dir224_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 .east p = true := by
  change ((!walkGuard soko2_2.board support p 224 225 .east || decide (bonus 224 p ≤ bonus 225 p)) && ((PreciseRolling.stayTargets soko2_2.board 225 .east).all (fun landing => !pushGuard support p 224 225 226 landing || decide (bonus 224 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 225 + bonus 225 (change p 225 (some landing)))) && (pushTargets soko2_2.board 225 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 224 225 226 landing || decide (bonus 224 p ≤ 1 - Generated.soko2_2Potential.boulder 225 - Generated.soko2_2Potential.hole landing + bonus 225 (change p 225 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check929 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check930 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir224_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 .west p = true := by
  change ((!walkGuard soko2_2.board support p 224 223 .west || decide (bonus 224 p ≤ bonus 223 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check931 p, rfl⟩
theorem dir224_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 .northEast p = true := by
  rfl
theorem dir224_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 224 201 .northWest || decide (bonus 224 p ≤ bonus 201 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check932 p, rfl⟩
theorem dir224_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 224 247 .southEast || decide (bonus 224 p ≤ bonus 247 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check933 p, rfl⟩
theorem dir224_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 224 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 224 245 .southWest || decide (bonus 224 p ≤ bonus 245 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check934 p, rfl⟩
theorem dir225_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 .north p = true := by
  rfl
theorem dir225_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 .south p = true := by
  change ((!walkGuard soko2_2.board support p 225 247 .south || decide (bonus 225 p ≤ bonus 247 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check935 p, rfl⟩
theorem dir225_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 .east p = true := by
  change ((!walkGuard soko2_2.board support p 225 226 .east || decide (bonus 225 p ≤ bonus 226 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check936 p, rfl⟩
theorem dir225_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 .west p = true := by
  change ((!walkGuard soko2_2.board support p 225 224 .west || decide (bonus 225 p ≤ bonus 224 p)) && ((PreciseRolling.stayTargets soko2_2.board 224 .west).all (fun landing => !pushGuard support p 225 224 223 landing || decide (bonus 225 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 224 + bonus 224 (change p 224 (some landing)))) && (pushTargets soko2_2.board 224 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 225 224 223 landing || decide (bonus 225 p ≤ 1 - Generated.soko2_2Potential.boulder 224 - Generated.soko2_2Potential.hole landing + bonus 224 (change p 224 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check937 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check938 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir225_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 225 204 .northEast || decide (bonus 225 p ≤ bonus 204 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check939 p, rfl⟩
theorem dir225_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 225 202 .northWest || decide (bonus 225 p ≤ bonus 202 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check940 p, rfl⟩
theorem dir225_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 225 248 .southEast || decide (bonus 225 p ≤ bonus 248 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check941 p, rfl⟩
theorem dir225_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 225 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 225 246 .southWest || decide (bonus 225 p ≤ bonus 246 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check942 p, rfl⟩
theorem dir226_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 .north p = true := by
  change ((!walkGuard soko2_2.board support p 226 204 .north || decide (bonus 226 p ≤ bonus 204 p)) && ((PreciseRolling.stayTargets soko2_2.board 204 .north).all (fun landing => !pushGuard support p 226 204 182 landing || decide (bonus 226 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 204 + bonus 204 (change p 204 (some landing)))) && (pushTargets soko2_2.board 204 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 226 204 182 landing || decide (bonus 226 p ≤ 1 - Generated.soko2_2Potential.boulder 204 - Generated.soko2_2Potential.hole landing + bonus 204 (change p 204 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check943 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check944 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir226_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 .south p = true := by
  change ((!walkGuard soko2_2.board support p 226 248 .south || decide (bonus 226 p ≤ bonus 248 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check945 p, rfl⟩
theorem dir226_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 .east p = true := by
  rfl
theorem dir226_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 .west p = true := by
  change ((!walkGuard soko2_2.board support p 226 225 .west || decide (bonus 226 p ≤ bonus 225 p)) && ((PreciseRolling.stayTargets soko2_2.board 225 .west).all (fun landing => !pushGuard support p 226 225 224 landing || decide (bonus 226 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 225 + bonus 225 (change p 225 (some landing)))) && (pushTargets soko2_2.board 225 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 226 225 224 landing || decide (bonus 226 p ≤ 1 - Generated.soko2_2Potential.boulder 225 - Generated.soko2_2Potential.hole landing + bonus 225 (change p 225 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check946 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check947 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir226_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 .northEast p = true := by
  rfl
theorem dir226_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 .northWest p = true := by
  rfl
theorem dir226_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 226 249 .southEast || decide (bonus 226 p ≤ bonus 249 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check948 p, rfl⟩
theorem dir226_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 226 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 226 247 .southWest || decide (bonus 226 p ≤ bonus 247 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check949 p, rfl⟩
theorem dir240_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 .north p = true := by
  change ((!walkGuard soko2_2.board support p 240 218 .north || decide (bonus 240 p ≤ bonus 218 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check950 p, rfl⟩
theorem dir240_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 .south p = true := by
  change ((!walkGuard soko2_2.board support p 240 262 .south || decide (bonus 240 p ≤ bonus 262 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check951 p, rfl⟩
theorem dir240_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 .east p = true := by
  rfl
theorem dir240_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 .west p = true := by
  rfl
theorem dir240_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 .northEast p = true := by
  rfl
theorem dir240_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 .northWest p = true := by
  rfl
theorem dir240_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 .southEast p = true := by
  rfl
theorem dir240_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 240 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
