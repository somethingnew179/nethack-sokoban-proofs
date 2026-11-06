import NetHack.Sokoban22Refined85.Directions14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir181_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 .north p = true := by
  change ((!walkGuard soko2_2.board support p 181 159 .north || decide (bonus 181 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check741 p, rfl⟩
theorem dir181_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 .south p = true := by
  rfl
theorem dir181_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 .east p = true := by
  change ((!walkGuard soko2_2.board support p 181 182 .east || decide (bonus 181 p ≤ bonus 182 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check742 p, rfl⟩
theorem dir181_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 .west p = true := by
  change ((!walkGuard soko2_2.board support p 181 180 .west || decide (bonus 181 p ≤ bonus 180 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check743 p, rfl⟩
theorem dir181_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 181 160 .northEast || decide (bonus 181 p ≤ bonus 160 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check744 p, rfl⟩
theorem dir181_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 181 158 .northWest || decide (bonus 181 p ≤ bonus 158 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check745 p, rfl⟩
theorem dir181_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 181 204 .southEast || decide (bonus 181 p ≤ bonus 204 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check746 p, rfl⟩
theorem dir181_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 181 .southWest p = true := by
  change ((!walkGuard soko2_2.board support p 181 202 .southWest || decide (bonus 181 p ≤ bonus 202 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check747 p, rfl⟩
theorem dir182_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 .north p = true := by
  change ((!walkGuard soko2_2.board support p 182 160 .north || decide (bonus 182 p ≤ bonus 160 p)) && ((PreciseRolling.stayTargets soko2_2.board 160 .north).all (fun landing => !pushGuard support p 182 160 138 landing || decide (bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 160 + bonus 160 (change p 160 (some landing)))) && (pushTargets soko2_2.board 160 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 182 160 138 landing || decide (bonus 182 p ≤ 1 - Generated.soko2_2Potential.boulder 160 - Generated.soko2_2Potential.hole landing + bonus 160 (change p 160 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check748 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check749 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir182_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 .south p = true := by
  change ((!walkGuard soko2_2.board support p 182 204 .south || decide (bonus 182 p ≤ bonus 204 p)) && ((PreciseRolling.stayTargets soko2_2.board 204 .south).all (fun landing => !pushGuard support p 182 204 226 landing || decide (bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 204 + bonus 204 (change p 204 (some landing)))) && (pushTargets soko2_2.board 204 .south).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 182 204 226 landing || decide (bonus 182 p ≤ 1 - Generated.soko2_2Potential.boulder 204 - Generated.soko2_2Potential.hole landing + bonus 204 (change p 204 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check750 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check751 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir182_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 .east p = true := by
  rfl
theorem dir182_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 .west p = true := by
  change ((!walkGuard soko2_2.board support p 182 181 .west || decide (bonus 182 p ≤ bonus 181 p)) && ((PreciseRolling.stayTargets soko2_2.board 181 .west).all (fun landing => !pushGuard support p 182 181 180 landing || decide (bonus 182 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 181 + bonus 181 (change p 181 (some landing)))) && (pushTargets soko2_2.board 181 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 182 181 180 landing || decide (bonus 182 p ≤ 1 - Generated.soko2_2Potential.boulder 181 - Generated.soko2_2Potential.hole landing + bonus 181 (change p 181 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check752 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check753 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir182_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 182 161 .northEast || decide (bonus 182 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check754 p, rfl⟩
theorem dir182_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 182 159 .northWest || decide (bonus 182 p ≤ bonus 159 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check755 p, rfl⟩
theorem dir182_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 .southEast p = true := by
  rfl
theorem dir182_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 182 .southWest p = true := by
  rfl
theorem dir184_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 .north p = true := by
  change ((!walkGuard soko2_2.board support p 184 162 .north || decide (bonus 184 p ≤ bonus 162 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check756 p, rfl⟩
theorem dir184_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 .south p = true := by
  rfl
theorem dir184_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 .east p = true := by
  change ((!walkGuard soko2_2.board support p 184 185 .east || decide (bonus 184 p ≤ bonus 185 p)) && ((PreciseRolling.stayTargets soko2_2.board 185 .east).all (fun landing => !pushGuard support p 184 185 186 landing || decide (bonus 184 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 185 + bonus 185 (change p 185 (some landing)))) && (pushTargets soko2_2.board 185 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 184 185 186 landing || decide (bonus 184 p ≤ 1 - Generated.soko2_2Potential.boulder 185 - Generated.soko2_2Potential.hole landing + bonus 185 (change p 185 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check757 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check758 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir184_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 .west p = true := by
  rfl
theorem dir184_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 184 163 .northEast || decide (bonus 184 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check759 p, rfl⟩
theorem dir184_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 184 161 .northWest || decide (bonus 184 p ≤ bonus 161 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check760 p, rfl⟩
theorem dir184_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 .southEast p = true := by
  rfl
theorem dir184_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 184 .southWest p = true := by
  rfl
theorem dir185_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 .north p = true := by
  change ((!walkGuard soko2_2.board support p 185 163 .north || decide (bonus 185 p ≤ bonus 163 p)) && ((PreciseRolling.stayTargets soko2_2.board 163 .north).all (fun landing => !pushGuard support p 185 163 141 landing || decide (bonus 185 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 163 + bonus 163 (change p 163 (some landing)))) && (pushTargets soko2_2.board 163 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 185 163 141 landing || decide (bonus 185 p ≤ 1 - Generated.soko2_2Potential.boulder 163 - Generated.soko2_2Potential.hole landing + bonus 163 (change p 163 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check761 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check762 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir185_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 .south p = true := by
  rfl
theorem dir185_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 .east p = true := by
  change ((!walkGuard soko2_2.board support p 185 186 .east || decide (bonus 185 p ≤ bonus 186 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check763 p, rfl⟩
theorem dir185_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 .west p = true := by
  change ((!walkGuard soko2_2.board support p 185 184 .west || decide (bonus 185 p ≤ bonus 184 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check764 p, rfl⟩
theorem dir185_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 185 164 .northEast || decide (bonus 185 p ≤ bonus 164 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check765 p, rfl⟩
theorem dir185_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 185 162 .northWest || decide (bonus 185 p ≤ bonus 162 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check766 p, rfl⟩
theorem dir185_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 .southEast p = true := by
  rfl
theorem dir185_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 185 .southWest p = true := by
  rfl
theorem dir186_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 .north p = true := by
  change ((!walkGuard soko2_2.board support p 186 164 .north || decide (bonus 186 p ≤ bonus 164 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check767 p, rfl⟩
theorem dir186_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 .south p = true := by
  rfl
theorem dir186_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 .east p = true := by
  rfl
theorem dir186_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 .west p = true := by
  change ((!walkGuard soko2_2.board support p 186 185 .west || decide (bonus 186 p ≤ bonus 185 p)) && ((PreciseRolling.stayTargets soko2_2.board 185 .west).all (fun landing => !pushGuard support p 186 185 184 landing || decide (bonus 186 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 185 + bonus 185 (change p 185 (some landing)))) && (pushTargets soko2_2.board 185 .west).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 186 185 184 landing || decide (bonus 186 p ≤ 1 - Generated.soko2_2Potential.boulder 185 - Generated.soko2_2Potential.hole landing + bonus 185 (change p 185 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check768 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check769 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir186_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 .northEast p = true := by
  rfl
theorem dir186_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 .northWest p = true := by
  change ((!walkGuard soko2_2.board support p 186 163 .northWest || decide (bonus 186 p ≤ bonus 163 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check770 p, rfl⟩
theorem dir186_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 .southEast p = true := by
  rfl
theorem dir186_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 186 .southWest p = true := by
  rfl
theorem dir188_north (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 .north p = true := by
  change ((!walkGuard soko2_2.board support p 188 166 .north || decide (bonus 188 p ≤ bonus 166 p)) && ((PreciseRolling.stayTargets soko2_2.board 166 .north).all (fun landing => !pushGuard support p 188 166 144 landing || decide (bonus 188 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 166 + bonus 166 (change p 166 (some landing)))) && (pushTargets soko2_2.board 166 .north).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 188 166 144 landing || decide (bonus 188 p ≤ 1 - Generated.soko2_2Potential.boulder 166 - Generated.soko2_2Potential.hole landing + bonus 166 (change p 166 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check771 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check772 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir188_south (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 .south p = true := by
  change ((!walkGuard soko2_2.board support p 188 210 .south || decide (bonus 188 p ≤ bonus 210 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check773 p, rfl⟩
theorem dir188_east (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 .east p = true := by
  change ((!walkGuard soko2_2.board support p 188 189 .east || decide (bonus 188 p ≤ bonus 189 p)) && ((PreciseRolling.stayTargets soko2_2.board 189 .east).all (fun landing => !pushGuard support p 188 189 190 landing || decide (bonus 188 p ≤ 1 + Generated.soko2_2Potential.boulder landing - Generated.soko2_2Potential.boulder 189 + bonus 189 (change p 189 (some landing)))) && (pushTargets soko2_2.board 189 .east).all (fun landing => !soko2_2.initial.holes.contains landing || !pushGuard support p 188 189 190 landing || decide (bonus 188 p ≤ 1 - Generated.soko2_2Potential.boulder 189 - Generated.soko2_2Potential.hole landing + bonus 189 (change p 189 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check774 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check775 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir188_west (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 .west p = true := by
  rfl
theorem dir188_northEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 .northEast p = true := by
  change ((!walkGuard soko2_2.board support p 188 167 .northEast || decide (bonus 188 p ≤ bonus 167 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check776 p, rfl⟩
theorem dir188_northWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 .northWest p = true := by
  rfl
theorem dir188_southEast (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 .southEast p = true := by
  change ((!walkGuard soko2_2.board support p 188 211 .southEast || decide (bonus 188 p ≤ bonus 211 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check777 p, rfl⟩
theorem dir188_southWest (p : Pattern) : directionCheck soko2_2.board soko2_2.initial.holes Generated.soko2_2Potential support bonus 188 .southWest p = true := by
  rfl
end NetHack.Sokoban22Refined85
