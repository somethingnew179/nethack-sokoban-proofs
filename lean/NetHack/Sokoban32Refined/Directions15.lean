import NetHack.Sokoban32Refined.Directions14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem dir175_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 .north p = true := by
  change ((!walkGuard soko3_2.board support p 175 149 .north || decide (bonus 175 p ≤ bonus 149 p)) && ((PreciseRolling.stayTargets soko3_2.board 149 .north).all (fun landing => !pushGuard support p 175 149 123 landing || decide (bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 149 + bonus 149 (change p 149 (some landing)))) && (pushTargets soko3_2.board 149 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 175 149 123 landing || decide (bonus 175 p ≤ 1 - Generated.soko3_2Potential.boulder 149 - Generated.soko3_2Potential.hole landing + bonus 149 (change p 149 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check762 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check763 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir175_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 .south p = true := by
  change ((!walkGuard soko3_2.board support p 175 201 .south || decide (bonus 175 p ≤ bonus 201 p)) && ((PreciseRolling.stayTargets soko3_2.board 201 .south).all (fun landing => !pushGuard support p 175 201 227 landing || decide (bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 201 + bonus 201 (change p 201 (some landing)))) && (pushTargets soko3_2.board 201 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 175 201 227 landing || decide (bonus 175 p ≤ 1 - Generated.soko3_2Potential.boulder 201 - Generated.soko3_2Potential.hole landing + bonus 201 (change p 201 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check764 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check765 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir175_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 .east p = true := by
  change ((!walkGuard soko3_2.board support p 175 176 .east || decide (bonus 175 p ≤ bonus 176 p)) && ((PreciseRolling.stayTargets soko3_2.board 176 .east).all (fun landing => !pushGuard support p 175 176 177 landing || decide (bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some landing)))) && (pushTargets soko3_2.board 176 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 175 176 177 landing || decide (bonus 175 p ≤ 1 - Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.hole landing + bonus 176 (change p 176 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check766 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check767 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir175_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 .west p = true := by
  change ((!walkGuard soko3_2.board support p 175 174 .west || decide (bonus 175 p ≤ bonus 174 p)) && ((PreciseRolling.stayTargets soko3_2.board 174 .west).all (fun landing => !pushGuard support p 175 174 173 landing || decide (bonus 175 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 174 + bonus 174 (change p 174 (some landing)))) && (pushTargets soko3_2.board 174 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 175 174 173 landing || decide (bonus 175 p ≤ 1 - Generated.soko3_2Potential.boulder 174 - Generated.soko3_2Potential.hole landing + bonus 174 (change p 174 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check768 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check769 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir175_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 175 150 .northEast || decide (bonus 175 p ≤ bonus 150 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check770 p, rfl⟩
theorem dir175_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 175 148 .northWest || decide (bonus 175 p ≤ bonus 148 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check771 p, rfl⟩
theorem dir175_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 175 202 .southEast || decide (bonus 175 p ≤ bonus 202 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check772 p, rfl⟩
theorem dir175_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 175 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 175 200 .southWest || decide (bonus 175 p ≤ bonus 200 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check773 p, rfl⟩
theorem dir176_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 .north p = true := by
  change ((!walkGuard soko3_2.board support p 176 150 .north || decide (bonus 176 p ≤ bonus 150 p)) && ((PreciseRolling.stayTargets soko3_2.board 150 .north).all (fun landing => !pushGuard support p 176 150 124 landing || decide (bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 150 + bonus 150 (change p 150 (some landing)))) && (pushTargets soko3_2.board 150 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 176 150 124 landing || decide (bonus 176 p ≤ 1 - Generated.soko3_2Potential.boulder 150 - Generated.soko3_2Potential.hole landing + bonus 150 (change p 150 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check774 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check775 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir176_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 .south p = true := by
  change ((!walkGuard soko3_2.board support p 176 202 .south || decide (bonus 176 p ≤ bonus 202 p)) && ((PreciseRolling.stayTargets soko3_2.board 202 .south).all (fun landing => !pushGuard support p 176 202 228 landing || decide (bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 202 + bonus 202 (change p 202 (some landing)))) && (pushTargets soko3_2.board 202 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 176 202 228 landing || decide (bonus 176 p ≤ 1 - Generated.soko3_2Potential.boulder 202 - Generated.soko3_2Potential.hole landing + bonus 202 (change p 202 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check776 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check777 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir176_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 .east p = true := by
  change ((!walkGuard soko3_2.board support p 176 177 .east || decide (bonus 176 p ≤ bonus 177 p)) && ((PreciseRolling.stayTargets soko3_2.board 177 .east).all (fun landing => !pushGuard support p 176 177 178 landing || decide (bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some landing)))) && (pushTargets soko3_2.board 177 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 176 177 178 landing || decide (bonus 176 p ≤ 1 - Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.hole landing + bonus 177 (change p 177 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check778 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check779 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir176_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 .west p = true := by
  change ((!walkGuard soko3_2.board support p 176 175 .west || decide (bonus 176 p ≤ bonus 175 p)) && ((PreciseRolling.stayTargets soko3_2.board 175 .west).all (fun landing => !pushGuard support p 176 175 174 landing || decide (bonus 176 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 175 + bonus 175 (change p 175 (some landing)))) && (pushTargets soko3_2.board 175 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 176 175 174 landing || decide (bonus 176 p ≤ 1 - Generated.soko3_2Potential.boulder 175 - Generated.soko3_2Potential.hole landing + bonus 175 (change p 175 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check780 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check781 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir176_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 176 151 .northEast || decide (bonus 176 p ≤ bonus 151 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check782 p, rfl⟩
theorem dir176_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 176 149 .northWest || decide (bonus 176 p ≤ bonus 149 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check783 p, rfl⟩
theorem dir176_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 176 203 .southEast || decide (bonus 176 p ≤ bonus 203 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check784 p, rfl⟩
theorem dir176_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 176 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 176 201 .southWest || decide (bonus 176 p ≤ bonus 201 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check785 p, rfl⟩
theorem dir177_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 .north p = true := by
  change ((!walkGuard soko3_2.board support p 177 151 .north || decide (bonus 177 p ≤ bonus 151 p)) && ((PreciseRolling.stayTargets soko3_2.board 151 .north).all (fun landing => !pushGuard support p 177 151 125 landing || decide (bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 151 + bonus 151 (change p 151 (some landing)))) && (pushTargets soko3_2.board 151 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 177 151 125 landing || decide (bonus 177 p ≤ 1 - Generated.soko3_2Potential.boulder 151 - Generated.soko3_2Potential.hole landing + bonus 151 (change p 151 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check786 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check787 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir177_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 .south p = true := by
  change ((!walkGuard soko3_2.board support p 177 203 .south || decide (bonus 177 p ≤ bonus 203 p)) && ((PreciseRolling.stayTargets soko3_2.board 203 .south).all (fun landing => !pushGuard support p 177 203 229 landing || decide (bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 203 + bonus 203 (change p 203 (some landing)))) && (pushTargets soko3_2.board 203 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 177 203 229 landing || decide (bonus 177 p ≤ 1 - Generated.soko3_2Potential.boulder 203 - Generated.soko3_2Potential.hole landing + bonus 203 (change p 203 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check788 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check789 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir177_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 .east p = true := by
  change ((!walkGuard soko3_2.board support p 177 178 .east || decide (bonus 177 p ≤ bonus 178 p)) && ((PreciseRolling.stayTargets soko3_2.board 178 .east).all (fun landing => !pushGuard support p 177 178 179 landing || decide (bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some landing)))) && (pushTargets soko3_2.board 178 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 177 178 179 landing || decide (bonus 177 p ≤ 1 - Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.hole landing + bonus 178 (change p 178 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check790 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check791 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir177_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 .west p = true := by
  change ((!walkGuard soko3_2.board support p 177 176 .west || decide (bonus 177 p ≤ bonus 176 p)) && ((PreciseRolling.stayTargets soko3_2.board 176 .west).all (fun landing => !pushGuard support p 177 176 175 landing || decide (bonus 177 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 176 + bonus 176 (change p 176 (some landing)))) && (pushTargets soko3_2.board 176 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 177 176 175 landing || decide (bonus 177 p ≤ 1 - Generated.soko3_2Potential.boulder 176 - Generated.soko3_2Potential.hole landing + bonus 176 (change p 176 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check792 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check793 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir177_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 177 152 .northEast || decide (bonus 177 p ≤ bonus 152 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check794 p, rfl⟩
theorem dir177_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 177 150 .northWest || decide (bonus 177 p ≤ bonus 150 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check795 p, rfl⟩
theorem dir177_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 177 204 .southEast || decide (bonus 177 p ≤ bonus 204 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check796 p, rfl⟩
theorem dir177_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 177 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 177 202 .southWest || decide (bonus 177 p ≤ bonus 202 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check797 p, rfl⟩
theorem dir178_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 .north p = true := by
  change ((!walkGuard soko3_2.board support p 178 152 .north || decide (bonus 178 p ≤ bonus 152 p)) && ((PreciseRolling.stayTargets soko3_2.board 152 .north).all (fun landing => !pushGuard support p 178 152 126 landing || decide (bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 152 + bonus 152 (change p 152 (some landing)))) && (pushTargets soko3_2.board 152 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 178 152 126 landing || decide (bonus 178 p ≤ 1 - Generated.soko3_2Potential.boulder 152 - Generated.soko3_2Potential.hole landing + bonus 152 (change p 152 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check798 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check799 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir178_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 .south p = true := by
  change ((!walkGuard soko3_2.board support p 178 204 .south || decide (bonus 178 p ≤ bonus 204 p)) && ((PreciseRolling.stayTargets soko3_2.board 204 .south).all (fun landing => !pushGuard support p 178 204 230 landing || decide (bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 204 + bonus 204 (change p 204 (some landing)))) && (pushTargets soko3_2.board 204 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 178 204 230 landing || decide (bonus 178 p ≤ 1 - Generated.soko3_2Potential.boulder 204 - Generated.soko3_2Potential.hole landing + bonus 204 (change p 204 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check800 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check801 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir178_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 .east p = true := by
  change ((!walkGuard soko3_2.board support p 178 179 .east || decide (bonus 178 p ≤ bonus 179 p)) && ((PreciseRolling.stayTargets soko3_2.board 179 .east).all (fun landing => !pushGuard support p 178 179 180 landing || decide (bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some landing)))) && (pushTargets soko3_2.board 179 .east).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 178 179 180 landing || decide (bonus 178 p ≤ 1 - Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.hole landing + bonus 179 (change p 179 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check802 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check803 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir178_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 .west p = true := by
  change ((!walkGuard soko3_2.board support p 178 177 .west || decide (bonus 178 p ≤ bonus 177 p)) && ((PreciseRolling.stayTargets soko3_2.board 177 .west).all (fun landing => !pushGuard support p 178 177 176 landing || decide (bonus 178 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 177 + bonus 177 (change p 177 (some landing)))) && (pushTargets soko3_2.board 177 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 178 177 176 landing || decide (bonus 178 p ≤ 1 - Generated.soko3_2Potential.boulder 177 - Generated.soko3_2Potential.hole landing + bonus 177 (change p 177 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check804 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check805 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir178_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 178 153 .northEast || decide (bonus 178 p ≤ bonus 153 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check806 p, rfl⟩
theorem dir178_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 178 151 .northWest || decide (bonus 178 p ≤ bonus 151 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check807 p, rfl⟩
theorem dir178_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 178 205 .southEast || decide (bonus 178 p ≤ bonus 205 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check808 p, rfl⟩
theorem dir178_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 178 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 178 203 .southWest || decide (bonus 178 p ≤ bonus 203 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check809 p, rfl⟩
theorem dir179_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 .north p = true := by
  change ((!walkGuard soko3_2.board support p 179 153 .north || decide (bonus 179 p ≤ bonus 153 p)) && ((PreciseRolling.stayTargets soko3_2.board 153 .north).all (fun landing => !pushGuard support p 179 153 127 landing || decide (bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 153 + bonus 153 (change p 153 (some landing)))) && (pushTargets soko3_2.board 153 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 179 153 127 landing || decide (bonus 179 p ≤ 1 - Generated.soko3_2Potential.boulder 153 - Generated.soko3_2Potential.hole landing + bonus 153 (change p 153 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check810 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check811 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir179_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 .south p = true := by
  change ((!walkGuard soko3_2.board support p 179 205 .south || decide (bonus 179 p ≤ bonus 205 p)) && ((PreciseRolling.stayTargets soko3_2.board 205 .south).all (fun landing => !pushGuard support p 179 205 231 landing || decide (bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 205 + bonus 205 (change p 205 (some landing)))) && (pushTargets soko3_2.board 205 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 179 205 231 landing || decide (bonus 179 p ≤ 1 - Generated.soko3_2Potential.boulder 205 - Generated.soko3_2Potential.hole landing + bonus 205 (change p 205 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check812 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check813 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir179_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 .east p = true := by
  change ((!walkGuard soko3_2.board support p 179 180 .east || decide (bonus 179 p ≤ bonus 180 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check814 p, rfl⟩
theorem dir179_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 .west p = true := by
  change ((!walkGuard soko3_2.board support p 179 178 .west || decide (bonus 179 p ≤ bonus 178 p)) && ((PreciseRolling.stayTargets soko3_2.board 178 .west).all (fun landing => !pushGuard support p 179 178 177 landing || decide (bonus 179 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 178 + bonus 178 (change p 178 (some landing)))) && (pushTargets soko3_2.board 178 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 179 178 177 landing || decide (bonus 179 p ≤ 1 - Generated.soko3_2Potential.boulder 178 - Generated.soko3_2Potential.hole landing + bonus 178 (change p 178 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check815 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check816 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir179_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 .northEast p = true := by
  change ((!walkGuard soko3_2.board support p 179 154 .northEast || decide (bonus 179 p ≤ bonus 154 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check817 p, rfl⟩
theorem dir179_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 179 152 .northWest || decide (bonus 179 p ≤ bonus 152 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check818 p, rfl⟩
theorem dir179_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 .southEast p = true := by
  change ((!walkGuard soko3_2.board support p 179 206 .southEast || decide (bonus 179 p ≤ bonus 206 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check819 p, rfl⟩
theorem dir179_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 179 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 179 204 .southWest || decide (bonus 179 p ≤ bonus 204 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check820 p, rfl⟩
theorem dir180_north (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 .north p = true := by
  change ((!walkGuard soko3_2.board support p 180 154 .north || decide (bonus 180 p ≤ bonus 154 p)) && ((PreciseRolling.stayTargets soko3_2.board 154 .north).all (fun landing => !pushGuard support p 180 154 128 landing || decide (bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 154 + bonus 154 (change p 154 (some landing)))) && (pushTargets soko3_2.board 154 .north).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 180 154 128 landing || decide (bonus 180 p ≤ 1 - Generated.soko3_2Potential.boulder 154 - Generated.soko3_2Potential.hole landing + bonus 154 (change p 154 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check821 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check822 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir180_south (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 .south p = true := by
  change ((!walkGuard soko3_2.board support p 180 206 .south || decide (bonus 180 p ≤ bonus 206 p)) && ((PreciseRolling.stayTargets soko3_2.board 206 .south).all (fun landing => !pushGuard support p 180 206 232 landing || decide (bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 206 + bonus 206 (change p 206 (some landing)))) && (pushTargets soko3_2.board 206 .south).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 180 206 232 landing || decide (bonus 180 p ≤ 1 - Generated.soko3_2Potential.boulder 206 - Generated.soko3_2Potential.hole landing + bonus 206 (change p 206 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check823 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check824 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir180_east (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 .east p = true := by
  rfl
theorem dir180_west (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 .west p = true := by
  change ((!walkGuard soko3_2.board support p 180 179 .west || decide (bonus 180 p ≤ bonus 179 p)) && ((PreciseRolling.stayTargets soko3_2.board 179 .west).all (fun landing => !pushGuard support p 180 179 178 landing || decide (bonus 180 p ≤ 1 + Generated.soko3_2Potential.boulder landing - Generated.soko3_2Potential.boulder 179 + bonus 179 (change p 179 (some landing)))) && (pushTargets soko3_2.board 179 .west).all (fun landing => !soko3_2.initial.holes.contains landing || !pushGuard support p 180 179 178 landing || decide (bonus 180 p ≤ 1 - Generated.soko3_2Potential.boulder 179 - Generated.soko3_2Potential.hole landing + bonus 179 (change p 179 none))))) = true
  refine Bool.and_eq_true_iff.mpr ⟨check825 p, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨check826 p, (by intro cell member; cases member)⟩)
  · exact List.all_eq_true.mpr (List.forall_mem_cons.mpr ⟨(by rfl), (by intro cell member; cases member)⟩)
theorem dir180_northEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 .northEast p = true := by
  rfl
theorem dir180_northWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 .northWest p = true := by
  change ((!walkGuard soko3_2.board support p 180 153 .northWest || decide (bonus 180 p ≤ bonus 153 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check827 p, rfl⟩
theorem dir180_southEast (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 .southEast p = true := by
  rfl
theorem dir180_southWest (p : Pattern) : directionCheck soko3_2.board soko3_2.initial.holes Generated.soko3_2Potential support bonus 180 .southWest p = true := by
  change ((!walkGuard soko3_2.board support p 180 205 .southWest || decide (bonus 180 p ≤ bonus 205 p)) && true) = true
  exact Bool.and_eq_true_iff.mpr ⟨check828 p, rfl⟩
end NetHack.Sokoban32Refined
