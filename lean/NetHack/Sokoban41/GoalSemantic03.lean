/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GoalSemantic02
import NetHack.Sokoban41.Rows
import NetHack.Sokoban41.Projection
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open Diagram
theorem goal0_shape12 (e f g h i j : Bool) : d793 (⟨true,true,false,false,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨true,true,false,false,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨true,true,false,false,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape12 (e f g h i j : Bool) : d800 (⟨true,true,false,false,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨true,true,false,false,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape12 (e f g h i j : Bool) : d816 (⟨true,true,false,false,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨true,true,false,false,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape13 (e f g h i j : Bool) : d793 (⟨true,true,false,true,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨true,true,false,true,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨true,true,false,true,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape13 (e f g h i j : Bool) : d800 (⟨true,true,false,true,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨true,true,false,true,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape13 (e f g h i j : Bool) : d816 (⟨true,true,false,true,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨true,true,false,true,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape14 (e f g h i j : Bool) : d793 (⟨true,true,true,false,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨true,true,true,false,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨true,true,true,false,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape14 (e f g h i j : Bool) : d800 (⟨true,true,true,false,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨true,true,true,false,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape14 (e f g h i j : Bool) : d816 (⟨true,true,true,false,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨true,true,true,false,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape15 (e f g h i j : Bool) : d793 (⟨true,true,true,true,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨true,true,true,true,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨true,true,true,true,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape15 (e f g h i j : Bool) : d800 (⟨true,true,true,true,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨true,true,true,true,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape15 (e f g h i j : Bool) : d816 (⟨true,true,true,true,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨true,true,true,true,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
end NetHack.Sokoban41
