/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GoalDiagram
import NetHack.Sokoban41.Rows
import NetHack.Sokoban41.Projection
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open Diagram
theorem goal0_shape0 (e f g h i j : Bool) : d793 (⟨false,false,false,false,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨false,false,false,false,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨false,false,false,false,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape0 (e f g h i j : Bool) : d800 (⟨false,false,false,false,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨false,false,false,false,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape0 (e f g h i j : Bool) : d816 (⟨false,false,false,false,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨false,false,false,false,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape1 (e f g h i j : Bool) : d793 (⟨false,false,false,true,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨false,false,false,true,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨false,false,false,true,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape1 (e f g h i j : Bool) : d800 (⟨false,false,false,true,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨false,false,false,true,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape1 (e f g h i j : Bool) : d816 (⟨false,false,false,true,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨false,false,false,true,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape2 (e f g h i j : Bool) : d793 (⟨false,false,true,false,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨false,false,true,false,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨false,false,true,false,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape2 (e f g h i j : Bool) : d800 (⟨false,false,true,false,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨false,false,true,false,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape2 (e f g h i j : Bool) : d816 (⟨false,false,true,false,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨false,false,true,false,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape3 (e f g h i j : Bool) : d793 (⟨false,false,true,true,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨false,false,true,true,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨false,false,true,true,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape3 (e f g h i j : Bool) : d800 (⟨false,false,true,true,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨false,false,true,true,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape3 (e f g h i j : Bool) : d816 (⟨false,false,true,true,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨false,false,true,true,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
end NetHack.Sokoban41
