/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GoalSemantic01
import NetHack.Sokoban41.Rows
import NetHack.Sokoban41.Projection
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open Diagram
theorem goal0_shape8 (e f g h i j : Bool) : d793 (⟨true,false,false,false,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨true,false,false,false,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨true,false,false,false,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape8 (e f g h i j : Bool) : d800 (⟨true,false,false,false,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨true,false,false,false,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape8 (e f g h i j : Bool) : d816 (⟨true,false,false,false,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨true,false,false,false,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape9 (e f g h i j : Bool) : d793 (⟨true,false,false,true,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨true,false,false,true,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨true,false,false,true,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape9 (e f g h i j : Bool) : d800 (⟨true,false,false,true,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨true,false,false,true,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape9 (e f g h i j : Bool) : d816 (⟨true,false,false,true,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨true,false,false,true,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape10 (e f g h i j : Bool) : d793 (⟨true,false,true,false,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨true,false,true,false,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨true,false,true,false,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape10 (e f g h i j : Bool) : d800 (⟨true,false,true,false,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨true,false,true,false,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape10 (e f g h i j : Bool) : d816 (⟨true,false,true,false,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨true,false,true,false,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal0_shape11 (e f g h i j : Bool) : d793 (⟨true,false,true,true,e,f,g,h,i,j⟩ : Ten) = (if budgetGuard 0 (⟨true,false,true,true,e,f,g,h,i,j⟩ : Ten) && decide ((Projection.occupied (⟨true,false,true,true,e,f,g,h,i,j⟩ : Ten)).length ≤ 1) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem goal1_shape11 (e f g h i j : Bool) : d800 (⟨true,false,true,true,e,f,g,h,i,j⟩ : Ten) = (if decide ((support.filter (fun cell => known (⟨true,false,true,true,e,f,g,h,i,j⟩ : Ten) cell && !deadCells.contains cell)).length = 0) then 1 else 0) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
theorem cap_shape11 (e f g h i j : Bool) : d816 (⟨true,false,true,true,e,f,g,h,i,j⟩ : Ten) = min 10 (NetHack.Sokoban.LowerBounds.weightSum debt (Projection.occupied (⟨true,false,true,true,e,f,g,h,i,j⟩ : Ten))) := by
  cases e <;> cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
end NetHack.Sokoban41
