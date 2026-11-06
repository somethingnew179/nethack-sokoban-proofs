/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GoalSemantic00
import NetHack.Sokoban41.Rows
import NetHack.Sokoban41.Projection
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open Diagram
theorem goal0_shape4 (e f g h i j : Bool) : d793 (⟨false,true,false,false,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨false,true,false,false,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨false,true,false,false,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape4 (e f g h i j : Bool) : d800 (⟨false,true,false,false,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨false,true,false,false,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape4 (e f g h i j : Bool) : d816 (⟨false,true,false,false,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨false,true,false,false,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape5 (e f g h i j : Bool) : d793 (⟨false,true,false,true,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨false,true,false,true,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨false,true,false,true,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape5 (e f g h i j : Bool) : d800 (⟨false,true,false,true,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨false,true,false,true,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape5 (e f g h i j : Bool) : d816 (⟨false,true,false,true,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨false,true,false,true,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape6 (e f g h i j : Bool) : d793 (⟨false,true,true,false,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨false,true,true,false,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨false,true,true,false,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape6 (e f g h i j : Bool) : d800 (⟨false,true,true,false,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨false,true,true,false,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape6 (e f g h i j : Bool) : d816 (⟨false,true,true,false,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨false,true,true,false,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape7 (e f g h i j : Bool) : d793 (⟨false,true,true,true,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨false,true,true,true,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨false,true,true,true,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape7 (e f g h i j : Bool) : d800 (⟨false,true,true,true,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨false,true,true,true,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape7 (e f g h i j : Bool) : d816 (⟨false,true,true,true,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨false,true,true,true,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
end NetHack.Sokoban41
